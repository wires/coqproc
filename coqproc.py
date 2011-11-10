#! /usr/bin/env python

import sys, codecs

from lepl import *

class Comment(Node): pass
class Command(Node): pass

@trampoline_matcher_factory()
def make_pair(start, end, contents):
    '''Generate a matcher that checks start and end tags.
       `start` must match the start and return the "label"
       `end` must match the end and return the same "label"
       If end fails then contents is used instead (and the matcher
       repeats.
       The return value is a pair that contains the label and 
       the contents.''' 
    def matcher(support, stream0):
        (match, stream1) = yield start._match(stream0)
        label = match[0]
        result = []
        while True:
            # can we end?
            try:
                (match, stream2) = yield end._match(stream1)
                if match:
                    if match[0] == label:
                        yield ([(label, result)], stream2)
                        return
                    else:
                        support._info('end matched, but %s != %s' % (match[0], label))
            except StopIteration:
                support._info('failed to match end')
                pass
            # failed to end, so try matching contents instead
            (match, stream2) = yield contents._match(stream1)
            result += match
            support._info('matched %s: %s' % (match, result))
            stream1 = stream2
    return matcher

def build():
    # nested comments
    start    = Literal('(*')
    end      = Literal('*)')
    both     = Or(start, end)

    nested_comment = Delayed()
    contents = (nested_comment | ~Lookahead(both) & Any())[:]
    comment = start & contents & end > Comment
    nested_comment += comment

    # commands
    dot      = Literal('.')
    # command = Regexp("[^.]\.\s") > Command
    command = AnyBut(dot)[:,...] + dot & Lookahead(Eof() | Whitespace() | comment) > Command


    expr = (nested_comment | command)[:,~(Whitespace()[:])] & Eof() > Node

    return expr.get_parse()

def process(ifn, ofn):
    vfile = codecs.open(ifn, "r", "utf8")
    in_str = ''.join(vfile.readlines()).strip()
#    print in_str
    parse = build()
    out_str = parse(in_str)
    print out_str[0]

if __name__ == "__main__":
#   print build()(sys.argv[1].strip())[0]#"(*Bla*)Lemma test:x+y.(*Co(*Nested*)mm*)")[0]
#   sys.exit()

   n = len(sys.argv)
   if not 2 <= n <= 3:
       print "usage: coqproc INFILE [OUTFILE]"
       sys.exit(-1)

   ifn = sys.argv[1]
   if n == 2:
       ofn = ifn
   else:
       ofn = sys.argv[2]

   process(ifn, ofn)
    
