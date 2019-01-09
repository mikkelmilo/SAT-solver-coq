(** * Library file that should be used for the term projects of introduction
to functional programming 2015. This file is based on SfLib.v of Software
Foundations by Benjamin Pierce and others. *)

(** * From the Coq Standard Library *)

Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export NPeano.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)


(** * From Basics.v *)

Require String. Open Scope string_scope.

(** * From Logic.v *)
(**  Identifiers *)

(** We define a new inductive datatype [Id] so that we won't confuse
    identifiers and numbers. *)

Inductive id : Type :=
  Id : nat -> id.

Definition beq_id (x x' : id) : bool :=
  match x, x' with
  | Id y, Id y' => beq_nat y y'
  end.
Lemma beq_id_refl : forall x : id,
  true = beq_id x x.
Proof.
  intros x; destruct x as [y]; simpl; apply beq_nat_refl.
Qed.
Lemma beq_id_eq: forall x x' : id,
  true = beq_id x x' -> x = x'.
Proof.
  intros x x' H; destruct x as [y]; destruct x' as [y']; simpl in H.
  apply beq_nat_eq in H. rewrite H. reflexivity.
Qed.

(* Exercise 2.1 *)
Inductive form :=
  | var : id -> form
  | ftrue : form
  | ffalse : form
  | and : form -> form -> form
  | or : form -> form -> form
  | imp : form -> form -> form
  | neg : form -> form.


Bind Scope form_scope with form.
Infix "/\" := and : form_scope.
Infix "\/" := or : form_scope.
Infix "-->" := imp (at level 70) : form_scope.
Notation "'!' b" := (neg b) (at level 60) : form_scope.
Notation "'vId' b" := (var (Id b)) (at level 55) : form_scope.
Open Scope form_scope.

Compute (or ffalse ftrue).
Compute (ffalse \/ ftrue).

(* Exercise 2.2 *)
Definition X := vId 0.
Definition Y := vId 1.
Definition Z := vId 2.

Definition ex1 : form := (X \/ !Y) /\ (!X \/ Y).
(* to test that the introduced notation behaves correctly: *)
Example ex1_correct : ex1 = (and (or X (neg Y)) (or (neg X) Y)).
Proof. reflexivity. Qed.

Definition ex2 : form := !Y --> (X \/ Y).
Example ex2_correct : ex2 = imp (neg Y) (or X Y).
Proof. reflexivity. Qed.
 
(* Note that /\ and \/ are right-associative *)
Definition ex3 : form := X /\ !X /\ ftrue.
Example ex3_correct : ex3 = and X (and (neg X) ftrue).
Proof. unfold ex3. reflexivity. Qed.

Definition valuation := id -> bool.
Definition empty_valuation : valuation := fun x => false.
Definition override (V : valuation) (x : id) (b : bool) : valuation :=
  fun y => if  beq_id x y then b else V y.

(* Exercise 2.3 *)
Fixpoint  interp (V : valuation) (p : form) : bool :=
  match p with
  | ffalse => false
  | ftrue => true
  | var id => V id
  | and f1 f2 => (interp V f1) && (interp V f2)
  | or f1 f2 => (interp V f1) || (interp V f2)
  | imp f1 f2 => if (interp V f1) then (interp V f2) else true
  | neg f => negb (interp V f)
  end.


Definition  satisfiable (p : form) : Prop :=
  exists V : valuation , interp V p = true.

(* Exercise 2.4 *)
Lemma  test1 : satisfiable  ex1.
Proof.
  unfold satisfiable. unfold ex1.
  (* we choose X = Y = false *)
  exists empty_valuation. 
  simpl. reflexivity.
Qed.

Lemma  test2 : satisfiable ex2.
Proof.
  unfold satisfiable. unfold ex2.
  (* we choose X = true, Y = false *)
  exists (override empty_valuation (Id 0) (true)). 
  simpl. reflexivity.
Qed.



(* Exercise 2.5: find_valuation *)

(* first some helper functions and representations... *)

Fixpoint contains_id (i : id) (ids : list id) : bool :=
  match ids with
  | x :: xs =>  if beq_id x i then true else (contains_id i xs)
  | [] => false
  end.

(* takes two lists of ids and returns a a merged list with no duplicates *)
Fixpoint merge_id_lists (l1 l2 : list id) : list id :=
  match l1 with
  | x :: xs => if contains_id x l2 
    then (merge_id_lists xs l2)
    else (merge_id_lists xs (x :: l2))
  | [] => l2
 end.

Fixpoint form_ids_aux (p : form) (ids : list id) : list id :=
  match p with
  | ffalse => ids
  | ftrue => ids
  | var id => if (contains_id id ids) then ids else id :: ids
  | neg f => form_ids_aux f ids
  | and f1 f2 => 
    merge_id_lists (form_ids_aux f1 ids) (form_ids_aux f2 ids)
  | or f1 f2 =>
    merge_id_lists (form_ids_aux f1 ids) (form_ids_aux f2 ids)
  | imp f1 f2 => 
    merge_id_lists (form_ids_aux f1 ids) (form_ids_aux f2 ids)
  end.

Definition form_ids (p : form) : list id := form_ids_aux p [].
Definition assignment := list (id * bool).
Definition empty_assignment (p : form) : assignment :=
  map (fun id => (id, false)) (form_ids p).

(* 
  this function essentially models binary (big-endian) increment
  on the second element of the tuples.
*)
Fixpoint next_assignment (a : assignment) : assignment :=
  match a with
  | [] => []
  | (id, b) :: xs => if b
    then (id, false) :: next_assignment xs
    else (id, true) :: xs
  end. 

Example next_assignment_ex : next_assignment [(Id 1,true);(Id 2,true);(Id 3,false)] = [(Id 1,false);(Id 2,false);(Id 3,true)].
Proof.
(* input represents 110 (3 in decimal). output represents 001 (4 in decimal) *)
reflexivity.
Qed.

Definition is_all_true_assignment (a : assignment) : bool :=
  forallb (fun idb => match idb with (id, b) => b end) a.  

Definition assignment_to_valuation (a : assignment) : valuation :=
  let f := fun i => (fun x => match x with (id,v) => beq_id i id end)
  in fun (i : id) => match find (f i) a with
    | Some (_,v) => v 
    | None => false
    end.

(* check if the given assignment satisfies p. 
   If not, try the next assignment. Stop when assignment is all true *)
Fixpoint find_valuation_aux 
  (p : form) (a : assignment) (fuel : nat) : option valuation :=
  let V' := assignment_to_valuation a in
  match fuel with
  | 0 => if interp V' p 
      then Some V'
      else None
  | S n => if interp V' p
    then Some V'
    else find_valuation_aux p (next_assignment a) n
  end.

Definition find_valuation (p : form) : option valuation :=
  let fuel := (2^(length (form_ids p))) in
  find_valuation_aux p (empty_assignment p) fuel.

Definition solver (p : form) : bool :=
  match find_valuation p with
  | Some _ => true
  | None => false
  end.

(* Exercise 2.6 Explain the difference between satisfiable and solver *)
(* 
    Satisfiable is a proposition on formulae that describes when a formula is true.
    Solver is a function that essentially decides if the satisfiable property is true or
    not for a given formula.
*)

(* Exercise 2.7 Write 2 positive and 2 negative tests of the solver and prove these tests using the reflexivity tactic *)

Example pos_ex1 : solver (X /\ Y --> Y) = true.
Proof.
(* X = Y = true =>  false -> false, which is true *)
reflexivity.
Qed.

Example pos_ex2 : solver (Y --> !(Y \/ X --> (ftrue /\ ffalse))) = true.
Proof.
(* X = Y = true =>  false -> false, which is true *)
reflexivity.
Qed.

Example neg_ex3 : solver (X /\ !X \/ (ftrue --> ffalse)) = false.
Proof.
reflexivity.
Qed.

Example neg_ex4 : solver (X /\ !X) = false.
Proof.
reflexivity.
Qed.

Lemma find_valuation_aux_sound : forall p A V n,
  find_valuation_aux p A n = Some V -> satisfiable p.
Proof.
  intros. unfold satisfiable. generalize dependent A.
  induction n ; intros ; try unfold find_valuation_aux in H.
  - destruct (interp (assignment_to_valuation A) p) eqn:H1.
    + exists (assignment_to_valuation A).
      apply H1.
    + inversion H.
  - destruct (interp (assignment_to_valuation A) p) eqn:H1.
    + exists (assignment_to_valuation A).
      apply H1.
    + apply (IHn (next_assignment A)). apply H.
Qed.
  
Lemma find_valuation_sound : forall p V,
  find_valuation p = Some V -> satisfiable p.
Proof. 
  unfold find_valuation. intros. 
  apply (find_valuation_aux_sound p (empty_assignment p) V (2 ^ length (form_ids p))).
  apply H.
Qed.

(* Exercise 2.8 *)
Theorem  solver_sound : forall p,
  solver p = true -> satisfiable p.
Proof.
  unfold solver. intros.
  destruct (find_valuation p) eqn:H1.
  - apply (find_valuation_sound p v).
    apply H1.
  - inversion H. 
Qed.

(* Exercise 2.9: Negational Normal Form *)

Fixpoint nnf_aux (p : form) (fuel : nat) : form :=
  match fuel with
  | 0 => p
  | S n => match p with
    | ! ffalse => ftrue
    | ! ftrue => ffalse
    | ! var id => p
    | ! (f1 /\ f2) => (* de morgans law 1: ~(a /\ b) <=> ~a \/ ~b *)
      (nnf_aux (neg f1) n) 
      \/ (nnf_aux (neg f2) n)
    | ! (f1 \/ f2) => (* de morgans law 2: ~(a \/ b) <=> ~a /\ ~b *)
      (nnf_aux (neg f1) n) 
      /\ (nnf_aux (neg f2) n)
    | ! (f1 --> f2) => (* ~(f1 -> f2) <=> ~(~f1 \/ f2) <=> (f1 /\ ~f2 *)
      (nnf_aux f1 n) /\ (nnf_aux (neg f2) n)
    | !!f => nnf_aux f n  
    | f1 /\ f2 => 
      (nnf_aux f1 n) /\ (nnf_aux f2 n)
    | f1 \/ f2 => 
      (nnf_aux f1 n) \/ (nnf_aux f2 n)
    | f1 --> f2 => 
      (nnf_aux f1 n) --> (nnf_aux f2 n)
    | _ => p
    end
  end.


(* helper function to determine how much "gas" to use in the function 
  nnf_aux_aux *)
Fixpoint size_of_form (p : form) : nat :=
  match p with
  | ffalse => 1
  | ftrue => 1
  | var id => 1
  | f1 /\ f2 => (size_of_form f1) + (size_of_form f2)
  | f1 \/ f2 => (size_of_form f1) + (size_of_form f2)
  | f1 --> f2 => (size_of_form f1) + (size_of_form f2)
  | !f => S (size_of_form f)
  end.  

(* computes the negational normal form of a boolean formula *)
Definition nnf (p : form) : form := nnf_aux p (2 * size_of_form p).
Definition nnf_solver (p : form) : bool := solver (nnf p).

(* helper lemma for convenience *)
Lemma interp_neg_true_iff : forall p V,
  interp V (!p) = true <-> interp V p = false.
Proof.
  split; intros; simpl in *.
  - unfold negb in H.
    destruct (interp V p) eqn:Hp.
    + inversion H.
    + reflexivity.
  - unfold negb. rewrite H. reflexivity.
Qed.

(* a formula has the same truth table as its 
   computed negational normal form. 
*)
Lemma nnf_aux_sound_and_complete : forall p n V,
  interp V (nnf_aux p n) = true <-> interp V p = true.
Proof.
  intros. generalize dependent p. induction n; intros.
  - (* n = 0 *)
    split.
    + intros. apply H.
    + intros. apply H.
  - (* n' = S n *)
    destruct p; 
    (* try a lot of splitting and applying hypotheses in each case.
       Eliminates trivial cases such as ftrue, ffalse, and vId. *)
    try split; try intros; simpl; 
    try apply H;
    try apply andb_true_iff in H; try apply andb_true_iff; try apply H.
    + (* nnf (p1 /\ p2) -> (p1 /\ p2) *)
      rewrite IHn, IHn in H. apply H.
    + (* (p1 /\ p2) -> nnf (p1 /\ p2) *)
      rewrite IHn. rewrite IHn. apply H.
    + (* nnf (p1 \/ p2) -> (p1 \/ p2) *)
      apply orb_true_iff in H. 
      apply orb_true_iff. destruct H.
      left. apply IHn, H.
      right. apply IHn, H.
    + (* (p1 \/ p2) -> nnf (p1 \/ p2) *)
      apply orb_true_iff in H. apply orb_true_iff.
      destruct H.
      left. apply IHn, H.
      right. apply IHn, H.
    + (* nnf p1 --> p2 -> p1 --> p2 *)
      simpl in H. destruct (interp V p1) eqn:H1.
      * apply IHn. apply IHn in H1.   
        destruct (interp V (nnf_aux p1 n)) eqn:H2;
        try apply H; try inversion H1.
      * reflexivity.
    + (* p1 --> p2 -> nnf p1 --> p2 *)
      simpl in H. destruct (interp V (nnf_aux p1 n)) eqn:H1; 
      try reflexivity.
      destruct (interp V p1) eqn:H2.
      * apply IHn. apply H.
      * rewrite IHn in H1. rewrite H1 in H2. inversion H2.
    + (* nnf !p -> !p *)
      assert (H_neg : forall p V, ~(interp V p = negb (interp V p))).
      {
        intros. simpl. unfold not. unfold negb.
        destruct (interp V0 p0) eqn:Hp; intros; inversion H0.
      }
      (* because of the structure of nnf_aux, we must destruct on the
         "inner" match of nnf_aux *)
      (* all the following are simply contradiction proofs *)
      unfold negb. destruct (interp V p) eqn:H1; try reflexivity.
      destruct p; simpl in *.
      * rewrite H1 in H. inversion H.
      * inversion H.
      * inversion H1.
      * apply orb_true_iff in H. 
        apply andb_true_iff in H1. destruct H1.
        destruct H.
        { rewrite IHn in H. simpl in H. rewrite H0 in H. inversion H. }
        { rewrite IHn in H. simpl in H. rewrite H1 in H. inversion H. }
      * apply andb_true_iff in H. destruct H.
        apply orb_true_iff in H1. destruct H1; simpl in *.
        { rewrite IHn in H. rewrite <- H in H1. inversion H1.
          apply H_neg in H3. inversion H3. }
        { rewrite IHn in H0. apply interp_neg_true_iff in H0.
          rewrite H1 in H0. inversion H0. }
      * apply andb_true_iff in H. destruct H.
        destruct (interp V p1) eqn:Hp1.
        { rewrite IHn in H0. rewrite <- H0 in H1. apply H_neg in H1.
          inversion H1. }
        { rewrite IHn in H. rewrite H in Hp1. inversion Hp1. } 
      * rewrite IHn in H. rewrite H in H1. simpl in H1. inversion H1.
    + (* !p -> nnf !p *)
      destruct p; simpl in *; try apply andb_true_iff.
      * apply H.
      * inversion H.
      * apply H.
      * apply orb_true_iff.
        rewrite negb_andb in H. apply orb_true_iff in H. destruct H.
        { left. apply IHn. apply H. }
        { right. apply IHn. apply H. }
      * rewrite negb_orb in H. apply andb_true_iff in H.
        rewrite negb_true_iff, negb_true_iff in H.
        rewrite IHn, IHn. 
        rewrite interp_neg_true_iff, interp_neg_true_iff. 
        apply H.
      * destruct (interp V p1) eqn:Hp1.
        { split.
          + apply IHn. apply Hp1.
          + apply IHn.
            apply H.
        }
        { inversion H. }
      * apply IHn. apply negb_true_iff in H. 
        apply negb_false_iff.
        apply H.
Qed.


Lemma nnf_sound_and_complete : forall p,
  satisfiable (nnf p) <-> satisfiable p.
Proof.
  intros. unfold satisfiable.
  split; intros; destruct H;
  exists x. 
  - rewrite <- nnf_aux_sound_and_complete. apply H.
  - apply nnf_aux_sound_and_complete. apply H.
Qed.

Theorem nnf_solver_sound : forall p,
  nnf_solver p = true -> satisfiable p.
Proof.
  unfold nnf_solver.
  intros.
  apply solver_sound in H. apply nnf_sound_and_complete.
  apply H.
Qed.

(* --- QuickChick part --- *)
(* 
  The goal of the following is to QuickCheck completeness of the solver,
  and to construct an optimizing shrinker for forms
*)
From QuickChick Require Import QuickChick. Import QcNotation.
Set Warnings "-extraction-opaque-accessed,-extraction".
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.

Derive Show for id.
Derive Arbitrary for id.

Derive Show for form.
(* 
  form cannot construct any syntactically or semantically
  invalid boolean formulae, so we can just derive its generator,
  however we don't expect the generated shrinker to exploit the
  semantics of forms, so we make one ourselves.
*)
Derive Arbitrary for form.
Print GenSizedform.
Print GenSized.

Definition genFormSized (n : nat) : G form :=
  arbitrarySized n.

Sample (genFormSized 4).
(* ===>
  QuickChecking (genFormSized 5)
  [
  (ffalse /\ ffalse /\ ffalse) /\ 
    ((ftrue /\ ffalse) /\ ffalse \/ ftrue --> 
      vId 5 \/ vId 9 \/ ftrue);
  ftrue --> vId 4; 
  vId 3; ! (! (ftrue /\ ffalse \/ ffalse));
  ! (((ffalse \/ vId 1) \/ ! vId 2) \/ ffalse --> 
    (ftrue --> ftrue));
  ffalse --> 
    (ffalse /\ ! vId 3) /\ ftrue /\ ffalse /\ (vId 0 \/ ffalse);
  ! (ftrue /\ (ftrue \/ ftrue) /\ ffalse --> ftrue); 
  vId 2;
  ! (! (ftrue --> ffalse)) --> 
    ((vId 1 \/ vId 2 --> ftrue) \/ ffalse);
  ffalse --> ftrue \/ ffalse;
  (! (! ftrue) \/ ffalse) /\
  (ffalse /\ ffalse --> ftrue) --> (vId 0 --> vId 0)
  ]

  We see that the derived generator generates a lot of uninteresting formulae, particularly with many ffalse and ftrue constructors.
  Instead of these, we want identifiers to occurs more often, since these
  are what dictates the "complexity" of the formula. Below is a better generator.
*)

(* this generator never generates formulae with ffalse and ftrue
  (because they are reducible to equivalent formulae without them)
*)
Fixpoint genFormSizedBetter (n : nat) : G form :=
  match n with
  | 0 => (* gen. arbitrary identifier in interval [0;n] *) 
    liftM var (arbitrarySized n) 
  | S n' =>
    freq [
      (* a small frequency of forms will stop generation early at var,
         but most will contain non-trivial constructors 
         (and, or, -->, neg) *)
      (1, liftM var (arbitrarySized n)) ;
      (4, liftM2 and (genFormSizedBetter n') (genFormSizedBetter n')) ;
      (4, liftM2 or (genFormSizedBetter n') (genFormSizedBetter n')) ;
      (4, liftM2 imp (genFormSizedBetter n') (genFormSizedBetter n')) ;
      (4, liftM neg (genFormSizedBetter n'))
    ]
  end.

Sample (genFormSizedBetter 2).
(*
QuickChecking (genFormSizedBetter 2)
 ===> [
  vId 1; 
  ! (! vId 9); 
  ! (! vId 6); 
  (vId 0 /\ vId 1) /\ vId 0 /\ vId 2;
  ! vId 4 /\ (vId 4 \/ vId 2); 
  vId 1 /\ (vId 5 \/ vId 2);
  ! vId 4 --> ! vId 1; 
  ! (! vId 2); 
  vId 0 --> ! vId 2;
  vId 0 --> vId 1 \/ vId 0 \/ vId 1; 
  ! (vId 0 --> vId 0)
]

  Much better.
*)

(* helper function *)
Definition combineShrunkPairs (f1s f2s : list form) : list form :=
  fold_left (fun acc f => 
    (map (fun r => f /\ r) f2s) ++ acc
  ) f1s [].

Fixpoint shrinkFormAux (p : form) : list form :=
  match p with
  | ffalse => [p]
  | ftrue => [p]
  | var id => [p]
  | and f1 f2 =>
    match (f1, f2) with
    | (ffalse,_) => [ffalse]
    | (_, ffalse) => [ffalse]
    | (ftrue, _) => shrinkFormAux f2
    | (_, ftrue) => shrinkFormAux f1
    | (_,_) => combineShrunkPairs (shrinkFormAux f1) (shrinkFormAux f2)
    end
  | or f1 f2 =>
    match (f1, f2) with
    | (ftrue,_) => [ftrue]
    | (_, ftrue) => [ftrue]
    | (ffalse, _) => shrinkFormAux f2
    | (_, ffalse) => shrinkFormAux f1
    | (_,_) => combineShrunkPairs (shrinkFormAux f1) (shrinkFormAux f2)
    end 
  | f1 --> f2 =>
    match (f1, f2) with
    | (ffalse, _) => [ftrue]
    | (ftrue, _) =>  shrinkFormAux f2
    | (_,_) => 
      let f1s := (shrinkFormAux f1) in
      let f2s := (shrinkFormAux f2) in
      match f1s with
      | [ftrue] => shrinkFormAux f2 
      | [ffalse] => [ftrue]
      | _ => combineShrunkPairs f1s f2s
      end 
    end
  | neg f =>
    match f with
    | ftrue => [ffalse]
    | ffalse => [ftrue]
    | _ => map (fun r => !r) (shrinkFormAux f)
    end
  end.

Instance shrinkForm : Shrink form := 
  {| shrink x := shrinkFormAux x |}.

(* sanity check *)
Compute (shrink ((X /\ ffalse) --> ftrue)).
(* ===>
    = [ftrue]
   : list form
*)

(* 
  Next we define a generator for a assignments.
  This is implemented by simply making a uniformly random assignment
  of truth values to the given identifiers.
*)

Fixpoint genAssignment (ids : list id) : G assignment :=
  let genIdBoolPair := 
    (fun (i : id) => oneOf [ 
      ret (i, false) ;
      ret (i, true) 
      ]) 
  in
  match ids with
  | [] => ret []
  | i :: ids' => liftM2 cons (genIdBoolPair i) (genAssignment ids') 
  end.

(* 
  Checking for actual satisfiability poses some problems because
  the satisfiable proposition does not implement the Decidable typeclass.
  The issue is that the satisfiable proposition quantifies over the set of
  valuations, which is infinite. However, since we know there is only a finite number of unique valuations for a given formula (albeit exponential
  in the size of the formula), I believe it should technically be possible
  to manually implementing this typeclass by proving completeness
  of interp (I have only proved soundness). This could be a very demanding task, so I have instead opted for a weaker notion of completeness, by showing that if (interp V p) evaluates to true (which is a decidable term, since all valid terms in Coq must terminate)
  then the solver also finds a valuation for p.
*)
Definition solver_pseudo_complete (p : form) (V : valuation) :=
  (interp V p) ==> (solver p).

(* we expect this to be false. We use this for sanity checking *)
Definition false_solver_pseudo_complete (p : form) (V : valuation) :=
  (interp V p) ==> negb(solver p).

Definition sanity_check_solver :=
  (forAllShrink 
    (genFormSizedBetter 1) 
    shrink
    (fun p => 
      forAll
      (genAssignment (form_ids p))
      (fun A =>
        false_solver_pseudo_complete p (assignment_to_valuation A)
      )
    )
  ).
QuickChick sanity_check_solver.
(*
  QuickChecking sanity_check_solver
  neg (var (Id 0))
  [(Id 0,false)]
  *** Failed after 1 tests and 0 shrinks. (0 discards)

  Sanity check succesful because the formula !X with valuation X=false
  interprets to true, and the solver does indeed find such a valuation.
*)

(* Now comes the real deal... *)

QuickChick 
  (forAllShrink 
    (genFormSizedBetter 4) 
    shrink
    (fun p => 
      forAll
      (genAssignment (form_ids p))
      (fun A =>
        solver_pseudo_complete p (assignment_to_valuation A)
      )
    )
  ).

(*
QuickChecking (forAllShrink (genFormSizedBetter 4) shrink
   (fun p =>
    forAll (genAssignment (form_ids p))
      (fun A => solver_pseudo_complete p (assignment_to_valuation A))))
+++ Passed 10000 tests (7198 discards)
*)
(*
  All passed, however we see that there are a lot of discards.
  We could try to construct an even smarter formula generator. 
  Ideally we want a generator only for satisfiable formulae, 
  however this problem is NP-hard (because then we would be able to solve the satisfiability problem efficiently as well), so I would expect QuickChicking with such a generator to be too slow for non-trivially-sized formulae. Therefore I have not implemented it.
*)

Close Scope form_scope.












