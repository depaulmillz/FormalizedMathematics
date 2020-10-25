Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.

Definition group_closure {X : Type} (A : Ensemble X) (op : X -> X -> X) := 
    forall x y: X, A x /\ A y -> A (op x y).

Definition group_associativity {X : Type} (A : Ensemble X) (op : X -> X -> X) := 
    forall x y z : X, A x /\ A y /\ A z -> op (op x y) z = op x (op y z).

Definition group_identity {X : Type} (e : X) (A : Ensemble X) (op : X -> X -> X) := 
    forall x : X, A x -> op x e = op e x /\ op x e = x /\ op e x = x.

Definition group_inverse {X : Type} (e : X) (A : Ensemble X) (op : X -> X -> X) := 
    forall x : X, A x -> exists x_inv, op x x_inv = e /\ op x_inv x = e.

Definition EmptyBoolSet : Ensemble bool := 
    Empty_set bool.

Definition BoolSet : Ensemble bool := Full_set bool.

Theorem All_in_BoolSet : forall x : bool, In bool BoolSet x.
Proof.
    unfold In.
    unfold BoolSet.
    apply Full_intro.
Qed.

Theorem Bool_closed : group_closure BoolSet xorb.
Proof.
    unfold group_closure.
    intros x y H.
    apply All_in_BoolSet.
Qed.

Theorem Bool_associative : group_associativity BoolSet xorb.
Proof.
    unfold group_associativity.
    intros x y z H.
    apply xorb_assoc_reverse.
Qed.

Theorem Bool_identity : group_identity false BoolSet xorb.
Proof.
    unfold group_identity.
    intros x H.
    rewrite xorb_false_r.
    rewrite xorb_false_l.
    split; try split; reflexivity.
Qed.

Theorem Bool_inverse : group_inverse false BoolSet xorb.
Proof.
    unfold group_inverse.
    intros x H.
    destruct x.
    - exists true. split; reflexivity.
    - exists false. split; reflexivity.
Qed.

Definition Group {X : Type} (S : Ensemble X) (op : X -> X -> X) (e : X) :=
group_closure S op /\ group_associativity S op /\ group_identity e S op /\ group_inverse e S op.

Theorem BooleanGroup : Group BoolSet xorb false.
Proof.
    unfold Group.
    split. 
    apply Bool_closed.
    split.
    apply Bool_associative.
    split.
    apply Bool_identity.
    apply Bool_inverse.
Qed.

Definition plus_mod_n (n x y : nat) := (plus x y) mod n.

Fixpoint Numbers0Ton (n : nat) (S : Ensemble nat) :=
match n with
| 0 => Add nat S 0
| S n' => Add nat (Numbers0Ton n' S) n
end.

Definition Zn (n : nat) := 
match n with
| 0 => Empty_set nat
| S n' => Numbers0Ton n' (Empty_set nat)
end.

Theorem m_lt_n_in_Zn : forall n m, m < n -> In nat (Zn n) m.
Proof.
  intros.
  induction n.
  - lia.
  - assert(H' : m < n \/ m = n). { lia. }
    destruct H'.
    + apply IHn in H0.
      destruct n.
      simpl in H0.
      contradiction.
      simpl.
      apply Union_introl.
      apply H0.
    + destruct n; 
      apply Union_intror; 
      rewrite H0;
      apply In_singleton.
Qed.

Theorem Zn_set_equivalence : forall n : nat, Zn (S n) = Add nat (Zn n) n.
Proof.
  intros.
  apply Extensionality_Ensembles.
  induction n.
  {
    split.
    - unfold Included.
      intros.
      simpl.
      simpl in H.
      apply H.
    - unfold Included.
      intros.
      simpl.
      simpl in H.
      apply H.
  }
  {
    apply Extensionality_Ensembles in IHn.
    split.
    - intros x H.
      simpl.
      simpl in H.
      apply H.
    - intros x H.
      apply H.
  }
Qed.


Theorem m_in_Zn_m_lt_n : forall n m, In nat (Zn n) m -> m < n.
Proof.
  intros.
  induction n.
  - simpl in H. apply Noone_in_empty in H. contradiction.
  - assert(H0: Zn (S n) = Add nat (Zn n) n). { apply Zn_set_equivalence. }
    assert(H1 : In nat (Zn n) m \/ m = n). 
    {
      rewrite H0 in H.
      induction H.
      - left. apply H.
      - right. 
        apply Singleton_inv in H.
        lia.
    }
    destruct H1.
    + apply IHn in H1. lia.
    + lia. 
Qed.

Definition group_homomorphism {X Y : Type} (G1 : Ensemble X) (op1 : X -> X -> X) (e1 : X)
(G2 : Ensemble Y) (op2 : Y -> Y -> Y) (e2 : Y) (f : X -> Y) : Prop :=
Group G1 op1 e1 /\ Group G2 op2 e2 -> forall (x y : X), G1 x /\ G1 y -> f (op1 x y) = op2 (f x) (f y) /\ G2 (f x) /\ G2 (f y).

Theorem mod_lt_n : forall x n, x < S n -> x mod (S n) = x.
Proof.
Admitted.
      
Theorem mod_plus : forall n x y, x mod S n + y mod (S n) = (x + y) mod S n.
Proof.
  intros.
Admitted.

Theorem mod_mod : forall n x, (x mod S n) mod S n = x mod S n.
Admitted.

Theorem In_Zn_iff_lt_n : forall n x, x < n <-> Zn n x.
Admitted. 

Theorem n_mod_n : forall n, n <> 0 -> n mod n = 0.
Proof.
Admitted.

Theorem plus_mod_n_3 : forall n x y z, 
plus_mod_n (S n) (plus_mod_n (S n) x y) z = (x + y + z) mod (S n).
Proof.
  intros.
  unfold plus_mod_n.
  remember (x + y) as w.
  rewrite <- mod_plus.
  rewrite mod_mod.
  rewrite mod_plus.
  reflexivity.
Qed.    

Theorem ZnGroup : forall n, n <> 0 -> Group (Zn n) (plus_mod_n n) 0.
Proof.
    unfold Group.
    intros.
    destruct n.
    - contradiction.
    - split.
      unfold group_closure.
      intros.
      simpl.
      induction n.
      simpl.
      apply Add_intro2.
      assert(S n <> 0). {
        lia.
      }
      induction (x+y); simpl.
      assert(H' : n - n = 0). { lia. }
      rewrite H'.
      assert(H'' : Add nat (Numbers0Ton n (Empty_set nat)) (S n) = Zn (S (S n))).
      {
        reflexivity.
      }
      rewrite H''.
      assert(H''' : 0 < S (S n)).
      {
        lia.
      }
      apply m_lt_n_in_Zn in H'''.
      apply H'''.
      destruct (snd (Init.Nat.divmod n0 (S n) 0 n)).
      apply Add_intro2.
      assert(H'' : Add nat (Numbers0Ton n (Empty_set nat)) (S n) = Zn (S (S n))).
      {
        reflexivity.
      }
      rewrite H''.
      apply m_lt_n_in_Zn.
      lia.
      split.
      simpl.
      unfold group_associativity.
      intros.
      destruct H0.
      destruct H1.
      rewrite plus_mod_n_3.
      unfold plus_mod_n.
      replace ((x + y + z)) with ((x + (y + z))).
      remember (y + z) as w.
      rewrite <- mod_plus.
      replace (x + w mod S n) with (w mod S n + x).
      rewrite <- mod_plus.
      rewrite mod_mod.
      replace (x mod S n + w mod S n) with (w mod S n + x mod S n).
      reflexivity.
      lia.
      lia.
      lia.
      split.
      unfold group_identity.
      intros.
      split.
      unfold plus_mod_n.
      replace (x + 0) with x.
      replace (0 + x) with x.
      reflexivity.
      lia.
      lia.
      split.
      unfold plus_mod_n.
      replace (x + 0) with x.
      apply mod_lt_n.
      simpl.
      apply In_Zn_iff_lt_n.
      apply H0.
      lia.
      unfold plus_mod_n.
      replace (0 + x) with x.
      apply mod_lt_n.
      apply In_Zn_iff_lt_n.
      apply H0.
      lia.
      unfold group_inverse.
      intros.
      exists (S n - x).
      split.
      unfold plus_mod_n.
      assert(H' : x < S n).
      {
        apply In_Zn_iff_lt_n in H0.
        apply H0.
      }
      assert(x + (S n - x) = S n). { lia. }
      rewrite H1.
      apply n_mod_n.
      apply H.
      unfold plus_mod_n.
      assert(H' : x < S n).
      {
        apply In_Zn_iff_lt_n in H0.
        apply H0.
      }
      assert(S n - x + x = S n). { lia. }
      rewrite H1.
      apply n_mod_n.
      lia.
Qed.

Theorem Z2_Group : Group (Zn 2) (plus_mod_n 2) 0.
Proof.
 apply ZnGroup.
 lia.
Qed.

Definition Bool_Z2_Map (x : bool) : nat :=
match x with
| false => 0
| true => 1
end.


Theorem Bool_Z2_Homomorphism : group_homomorphism 
BoolSet xorb false 
(Zn 2) (plus_mod_n 2) 0
Bool_Z2_Map.
Proof.
  unfold group_homomorphism.
  intros.
  unfold plus_mod_n.
  destruct x; destruct y; try simpl; repeat (try split; try reflexivity; try apply Add_intro2; try apply Add_intro1).
Qed.      
    
