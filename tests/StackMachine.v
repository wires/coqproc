Require Import List Tactics.
Set Implicit Arguments.

Require Import Utf8.

(** Source language, simple arithmetic expressions *)

Inductive binop : Set := Plus | Times.

Inductive exp : Set :=
  | Const : nat → exp
  | Binop : binop → exp → exp → exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Times => mult
  end.

Fixpoint expDenote (e : exp) : nat :=
  match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

(** Target language, simple stack machine *)

(** Push constant onto stack *)
(** Pop two constants, apply binary op and push result back onto the stack *)
Inductive instr : Set :=
  | IConst : nat -> instr
  | IBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

(* apply [instr]uction to [stack], returns [option stack] to deal
   with stack underflow *) 
Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
    | IConst n => Some (n :: s)
    | IBinop b =>
      match s with
        | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
        | _ => None
      end
  end.

(* Execute a program and return the resulting stack *)
Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
    | nil => Some s
    | i :: p' =>
      match instrDenote i s with
        | None => None
        | Some s' => progDenote p' s'
      end
  end.

(** Translation *)
Fixpoint compile (e : exp) : prog :=
  match e with
    | Const n => IConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ IBinop b :: nil
  end.

Definition example1 :=  Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7).

(* (2*2)*7 = 28 *)
Eval simpl in progDenote (compile example1) nil.

Theorem compile_correct : ∀ e,
  progDenote (compile e) nil = Some (expDenote e :: nil).
Proof.
 
Lemma compile_correct' : forall e p s,
  progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Proof.
  induction e.
   now reflexivity. 
  intros.
  simpl.
  rewrite <- app_assoc. rewrite IHe2.
  rewrite <- app_assoc. rewrite IHe1.
  reflexivity.
Qed.


(* coq supports:
(* nested comments*)
Extraction Language Haskell.
Extraction "compiler" compile.

*)
