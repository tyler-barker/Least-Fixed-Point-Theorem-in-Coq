Require Import Ensembles.
Require Import Partial_Order.
Require Import Relations_1.
Require Import Image.

Variable U : Type.

Inductive Bottom (U:Type)(P:PO U)(bot:U) : Prop :=
    Bottom_definition :
    In U (Carrier_of  U P) bot -> (forall y:U, (Rel_of U P) bot y) -> Bottom U P bot.

Inductive Upper_Bound (U:Type)(P:PO U)(B:Ensemble U) (x:U) : Prop :=
    Upper_Bound_definition :
    In U (Carrier_of U P) x -> (forall y:U, In U B y -> (Rel_of U P)  y x) -> Upper_Bound U P B x.

Inductive Lower_Bound (U:Type)(P:PO U)(B:Ensemble U) (x:U) : Prop :=
    Lower_Bound_definition :
    In U (Carrier_of U P) x -> (forall y:U, In U B y -> (Rel_of U P) x y) -> Lower_Bound U P B x.

Inductive Lub (U:Type)(P:PO U)(B:Ensemble U) (x:U) : Prop :=
    Lub_definition :
    Upper_Bound U P B x -> (forall y:U, Upper_Bound U P B y -> 
    (Rel_of U P) x y) -> Lub U P B x.

Inductive Glb (U:Type)(P:PO U)(B:Ensemble U) (x:U) : Prop :=
    Glb_definition :
    Lower_Bound U P B x -> (forall y:U, Lower_Bound U P B y -> 
    (Rel_of U P) y x) -> Glb U P B x.

Inductive Directed (U:Type)(P:PO U)(X:Ensemble U) : Prop :=
    Definition_of_Directed :
    Included U X (Carrier_of U P) ->
    Inhabited U X ->
    (forall x1 x2:U,
      Included U (Couple U x1 x2) X ->
      exists x3 : _, In U X x3 /\ Upper_Bound U P (Couple U x1 x2) x3) ->
    Directed U P X.

Inductive Complete (U:Type)(P:PO U) : Prop :=
    Definition_of_Complete :
    (exists bot : _, Bottom U P bot) ->
    (forall X:Ensemble U, Directed U P X -> exists bsup : _, Lub U P X bsup) ->
    Complete U P.

Record Poset : Type := Definition_of_poset {PO_of_poset : PO U}.

Inductive Monotone (A B:Poset)(h:U->U):Prop :=
Monotone_definition : 
(forall x:U, forall y:U, (Rel_of U (PO_of_poset A)) x y -> 
(Rel_of U (PO_of_poset B)) (h x) (h y)) -> Monotone A B h.

Theorem MonComp : forall A B C:Poset, forall j:U->U, forall k:U->U,
Monotone A B j -> Monotone B C k ->
Monotone A C (fun x: U => k (j x)).
intros. apply Monotone_definition. intros. elim H. intro. elim H0. intro.
apply H3. apply H2. exact H1. Save.

Fixpoint Chain (h:U->U) (x:U) (n:nat) {struct n}:U :=
match n with 
| 0 => x
| S p => h (Chain h x p)
end.

Definition ImChain (h:U->U)(x:U) := Im nat U (Full_set nat)(Chain h x). 

Theorem InChain: forall h:U->U, forall x:U, forall y:U, 
(In U (ImChain h x) y) -> exists n:nat,(Chain h x n)=y.
intros. unfold ImChain in H.
assert (exists n:nat, In nat (Full_set nat) n /\ (Chain h x n = y)).
apply Im_inv. exact H. elim H0. intros. elim H1. intros. exists x0.
exact H3. Save.

Theorem MonChain:forall P:Poset, forall k:U->U,forall x:U, forall n:nat,
Monotone P P k -> (Rel_of U (PO_of_poset P)) x (k x) ->
(Rel_of U (PO_of_poset P)) (Chain k x n) (Chain k x (n+1)).
intros. induction n. simpl. exact H0. simpl. apply H. exact IHn. Save.

Theorem Succ:forall n:nat, n<>0 -> exists m:nat, S m = n.
induction n. intro. contradict H. auto. intro. exists n. auto. Save.

Theorem MonChain2:forall P:Poset, forall k:U->U,forall x:U, forall n:nat, forall m:nat,
Monotone P P k -> (Rel_of U (PO_of_poset P)) x (k x) ->
(Rel_of U (PO_of_poset P)) (Chain k x n) (Chain k x (n+m)).
intros. induction n. simpl. induction m. simpl. elim (PO_of_poset P).
simpl in |- *. intros. elim PO_cond2. intros. apply H1.
assert (Rel_of U (PO_of_poset P) (Chain k x m)(Chain k x (S m))).
assert ((S m) = m+1). assert (m+1 = 1+m). auto with arith. rewrite H1. auto.
rewrite H1.
apply MonChain with (n:=m)(k:=k)(x:=x). exact H. exact H0.
assert (Order U (Rel_of U (PO_of_poset P))).
elim P. intros. simpl. apply PO_of_poset0. elim H2.
intros.
generalize H1. generalize IHm. apply H4. simpl.
apply H. exact IHn. Save. 

Require Import Arith.Plus.

Theorem LtSum:forall n:nat, forall m:nat, le n m -> exists x:nat, m=n+x.
intros. induction n. exists m. auto. assert (exists x : nat,m = n + x).
apply IHn. auto with arith. elim H0. intros.
assert (x <> 0). red. intro. contradict H. rewrite H1. rewrite H2.
compare (n) (n+0). intros. rewrite <- e. auto with arith.
intros. contradict n0. auto. assert (exists y:nat, S y = x).
apply Succ. exact H2.
elim H3. intros. exists x0. rewrite H1. rewrite <- H4. 
assert ((S n) + x0 = n + (S x0)).
apply plus_Snm_nSm with (n:=n)(m:=x0). auto. Save. 

Theorem MonChain3:forall P:Poset, forall k:U->U,forall x:U, forall n:nat, forall m:nat,
Monotone P P k -> (Rel_of U (PO_of_poset P)) x (k x) -> le n m ->
(Rel_of U (PO_of_poset P)) (Chain k x n) (Chain k x m).
intros. assert (exists x:nat, m=n+x). apply LtSum. exact H1.
elim H2. intros. rewrite H3. apply MonChain2. exact H. exact H0. Save.

Inductive PosetMap (A B:Poset)(h:U->U):Prop :=
PosetMap_definition :
(forall x:U, ((In U (Carrier_of U (PO_of_poset A)) x) -> 
(In U (Carrier_of U (PO_of_poset B))(h x)))) -> PosetMap A B h.

Theorem ChainInPoset: forall P:Poset, forall h:U->U, forall x:U, PosetMap P P h ->
(In U (Carrier_of U (PO_of_poset P)) x) ->
Included U (ImChain h x) (Carrier_of U (PO_of_poset P)).
intros. unfold Included. intros. unfold ImChain in H1. 
assert (exists n:nat, In nat (Full_set nat) n /\ Chain h x n = x0).
apply Im_inv. exact H1. elim H2.  intros. elim H3. intros. rewrite <- H5. clear H3.
clear H4. clear H5.  
induction x1. simpl. exact H0. simpl. generalize IHx1. 
intro.  elim H. intro. apply H3. exact IHx1. Save.

Require Import Arith.Max.

Theorem DirectedChain: forall P:Poset, forall h:U->U, PosetMap P P h -> 
Monotone P P h -> forall x:U, Bottom U (PO_of_poset P) x ->
Directed U (PO_of_poset P) (ImChain h x).
intros. apply Definition_of_Directed. unfold Included. intros.
unfold ImChain in H2. pose proof Im_inv. apply H3 in H2.
elim H2. intros. elim H4. intros. generalize H6. clear H4. 
clear H5. clear H6. induction x1.
simpl. intro. rewrite <- H6. apply H1. intros.
pose proof Im_def. 
assert (In U (ImChain h x) x0). unfold ImChain. rewrite <- H6.
apply Im_def. apply Full_intro. 
assert (Included U (ImChain h x) (Carrier_of U (PO_of_poset P))).
apply ChainInPoset. exact H. apply H1. unfold Included in H5.
apply H7. assumption. exists x. unfold ImChain. assert (x = (Chain h x 0)). 
simpl. auto. rewrite H2. apply Im_def. apply Full_intro. intros. 
unfold Included in H2. assert (In U (ImChain h x) x1). apply H2. apply Couple_l.
assert (In U (ImChain h x) x2). apply H2. apply Couple_r. unfold ImChain in H4.
unfold ImChain in H3. pose proof Im_inv. apply H5 in H3. apply H5 in H4.
elim H3. elim H4. intros.
elim H6. elim H7. intros. clear H7. clear H8.
exists (Chain h x (max x0 x3)).
split. apply Im_def. apply Full_intro. apply Upper_Bound_definition.
assert (Included U (ImChain h x) (Carrier_of U (PO_of_poset P))).
apply ChainInPoset. exact H. apply H1. unfold Included in H7. apply H7.
apply Im_def. apply Full_intro. intros. assert (In U (ImChain h x) y).
apply H2. exact H7. apply Im_inv in H8. 
elim H8. intros. elim H12. intros. clear H12. elim H7. rewrite <- H9.
apply MonChain3. exact H0. elim H0. intros. apply H1. auto with v62.
rewrite <- H11. apply MonChain3. exact H0. apply H1. intros. auto with v62.
Save.

Inductive PreservesSups (A B:Poset) (h:U->U):Prop :=
PreservesSups_definition: (forall X:Ensemble U, forall asup:U,
(Directed U (PO_of_poset A) X ->
Lub U (PO_of_poset A) X asup) -> 
Lub U (PO_of_poset B) (Im U U X h) (h asup)) ->
PreservesSups A B h.

Inductive ScottContinuous (A B:Poset) (h:U->U):Prop :=
ScottContinuous_definition: PosetMap A B h -> Monotone A B h 
-> PreservesSups A B h -> ScottContinuous A B h.

Inductive CPO (A:Poset):Prop :=
CPO_definition: Complete U (PO_of_poset A) -> CPO A.

Inductive LeastFixpoint (A:Poset)(h:U->U)(x:U):Prop :=
LeastFixpoint_definition: PosetMap A A h ->
In U (Carrier_of U (PO_of_poset A)) x ->
(h x) = x -> (forall y:U, In U (Carrier_of U (PO_of_poset A)) y ->
(h y) = y -> (Rel_of U (PO_of_poset A)) x y) ->
LeastFixpoint A h x.

Theorem ImDirected:forall P:Poset, forall h:U->U, forall X:Ensemble U,
Monotone P P h -> PosetMap P P h ->
Directed U (PO_of_poset P) X -> Directed U (PO_of_poset P) (Im U U X h).
intros. apply Definition_of_Directed. unfold Included. intros. apply Im_inv in H2. 
elim H2. intros. elim H3. intros. rewrite <- H5. apply H0. elim H1.
intros. apply H6. exact H4. elim H1. intros. elim H3.
intros. exists (h x). apply Im_def. exact H5. intros.  
assert (In U (Im U U X h) x1). unfold Included in H2. apply H2.
apply Couple_l. assert (In U (Im U U X h) x2). unfold Included in H2. apply H2.
apply Couple_r. apply Im_inv in H3. apply Im_inv in H4. 
elim H3. elim H4. intros. elim H5. elim H6. intros.
assert (exists y:U, In U X y /\ Upper_Bound U (PO_of_poset P) (Couple U x x0) y). elim H1.
intros. apply H13. unfold Included. intros. elim H14. 
exact H9. exact H7.
elim H11. intros. elim H12. intros. exists (h x3).
split. apply Im_def. exact H13. apply Upper_Bound_definition.
apply H0. apply H1. exact H13. intros. elim H15.
rewrite <- H8. apply H. apply H14.
apply Couple_r. intros. rewrite <- H10. apply H. apply H14.
apply Couple_l. Save.

Theorem Lubs: forall P:Poset, forall h:U->U, forall x y:U, Bottom U (PO_of_poset P) x -> 
Monotone P P h -> PosetMap P P h -> (Lub U (PO_of_poset P) (Im U U (ImChain h x) h) y -> 
Lub U (PO_of_poset P) (ImChain h x) y).
intros. apply Lub_definition. apply Upper_Bound_definition. elim H2. intros.
elim H3. intros. exact H5. intros. unfold ImChain in H3. apply Im_inv in H3.
elim H3. intros. elim H4. intros. rewrite <- H6. clear H4. clear H5. clear H6.
induction x0. simpl. apply H. apply H2. simpl. apply Im_def. apply Im_def. apply Full_intro.
intros. apply H2. apply Upper_Bound_definition. apply H3.
intros. assert (In U (ImChain h x) y1). unfold ImChain. apply Im_inv in H4.
elim H4. intros. elim H5. intros. 
unfold ImChain in H6. apply Im_inv in H6.  
elim H6. intros. elim H8. intros.
rewrite <- H7. rewrite <- H10.
assert (h (Chain h x x1) = (Chain h x (S x1))). simpl. auto. rewrite H11.
apply Im_def. apply Full_intro. apply H3. exact H5. Save.

Theorem LeastFixedPoint: forall P:Poset, forall h:U->U, ScottContinuous P P h ->
CPO P -> exists x:U, LeastFixpoint P h x.
intros. elim H0. intros. elim H1. intros. elim H2. intros.
assert (Directed U (PO_of_poset P) (ImChain h x)). 
apply DirectedChain with (x:=x)(h:=h). apply H. apply H. apply H4. 
assert (exists lub:U, Lub U (PO_of_poset P) (ImChain h x) lub). apply H1. apply H5. 
elim H6. intros.
exists x0. 
apply LeastFixpoint_definition. apply H. apply H7. elim H. intros.
elim H10. intros. assert (Directed U (PO_of_poset P) (Im U U (ImChain h x) h)).
apply Definition_of_Directed. unfold Included. intros.
assert (exists n:nat, In nat (Full_set nat) n /\ Chain h x n = x1).
apply Im_inv. unfold ImChain in H12. 
assert (exists y:U, In U (Im nat U (Full_set nat)(Chain h x)) y /\ h y = x1).
apply Im_inv. exact H12. elim H13. intros. elim H14. intros.
assert (exists n:nat, In nat (Full_set nat) n /\ Chain h x n = x2).
apply Im_inv. exact H15. elim H17. intros. elim H18. intros.
assert (Chain h x (S x3) = x1). simpl. rewrite H20. auto.
rewrite <- H21. apply Im_def. apply Full_intro. 
assert (Included U (ImChain h x) (Carrier_of U (PO_of_poset P))). apply ChainInPoset. assumption.
apply H4. unfold Included in H14. apply H14. unfold ImChain.
elim H13. intros. elim H15. intros. rewrite <- H17. apply Im_def.
apply Full_intro. exists (h x). apply Im_def. unfold ImChain.
assert (x = (Chain h x 0)). simpl. auto. rewrite H12. apply Im_def.
apply Full_intro. intros. assert (In U (Im U U (ImChain h x) h) x1).
apply H12. apply Couple_l. assert (In U (Im U U (ImChain h x) h) x2).
apply H12. apply Couple_r.
assert (exists n:nat, In nat (Full_set nat) n /\ Chain h x n = x1).
apply Im_inv. unfold ImChain in H13.
assert (exists y:U, In U (Im nat U (Full_set nat)(Chain h x)) y /\ h y = x1).
apply Im_inv. exact H13. elim H15. intros. elim H16. intros.
assert (exists n:nat, In nat (Full_set nat) n /\ Chain h x n = x3).
apply Im_inv. exact H17. elim H19. intros. elim H20. intros.
assert (Chain h x (S x4) = x1). simpl. rewrite H22. exact H18.
rewrite <- H23. apply Im_def. apply Full_intro. elim H15. intros. elim H16. intros.
assert (exists n:nat, In nat (Full_set nat) n /\ Chain h x n = x2).
apply Im_inv. unfold ImChain in H14.
assert (exists y:U, In U (Im nat U (Full_set nat)(Chain h x)) y /\ h y = x2).
apply Im_inv. exact H14. elim H19. intros. elim H20. intros.
assert (exists n:nat, In nat (Full_set nat) n /\ Chain h x n = x4).
apply Im_inv. exact H21. elim H23. intros. elim H24. intros.
assert (Chain h x (S x5) = x2). simpl. rewrite H26. exact H22.
rewrite <- H27. apply Im_def. apply Full_intro. elim H19. intros. elim H20. intros.
exists (Chain h x (max x3 x4)). assert ({max x3 x4=x3} + {max x3 x4=x4}). 
apply max_dec with (n:=x3)(m:=x4). elim H23. intros.
split. rewrite a. rewrite H18. assumption. apply Upper_Bound_definition.
rewrite a. assert (Included U (ImChain h x) (Carrier_of U (PO_of_poset P))). apply ChainInPoset. apply H. apply H4. apply H24. 
unfold ImChain. apply Im_def. apply Full_intro.
intros. assert (y=x1 \/ y=x2). auto with sets. elim H25. intros. rewrite H26. 
rewrite <- H18. apply MonChain3. apply H. apply H4. auto with v62. 
intros. rewrite H26. rewrite <- H22. apply MonChain3. apply H. apply H4. 
auto with arith. intros. split. rewrite b. rewrite H22. assumption. apply Upper_Bound_definition.
rewrite b. assert (Included U (ImChain h x) (Carrier_of U (PO_of_poset P))). apply ChainInPoset. apply H. apply H4.
apply H24. apply Im_def. apply Full_intro. intros. assert (y=x1 \/ y=x2). auto with sets.
elim H25. intros. rewrite H26. rewrite <- H18. apply MonChain3. apply H. apply H4. 
auto with arith. intros. rewrite H26. rewrite <- H22. apply MonChain3. apply H. apply H4.
auto with arith. assert (Lub U (PO_of_poset P) (Im U U (ImChain h x) h) (h x0)).
apply H11. intros. exact H7. assert (Lub U (PO_of_poset P) (ImChain h x)(h x0)).
apply Lubs. exact H4. exact H9. exact H8. exact H13.
assert ((Rel_of U (PO_of_poset P)) x0 (h x0)). apply H7. apply H14.
assert ((Rel_of U (PO_of_poset P)) (h x0) x0). apply H14. apply H7. generalize H15. generalize H16. 
assert (Antisymmetric U (Rel_of U (PO_of_poset P))). 
assert (Order U (Rel_of U (PO_of_poset P))).
apply PO_cond2. apply H17. apply H17. intros.
assert (Upper_Bound U (PO_of_poset P) (ImChain h x) y). apply Upper_Bound_definition.
 exact H8. intros. unfold ImChain in H10. 
assert (exists n:nat, In nat (Full_set nat) n /\ Chain h x n = y0).
apply Im_inv. exact H10. elim H11. intros. elim H12. intros. rewrite <- H14.
clear H12. clear H13. clear H14. induction x1. simpl. apply H4. simpl. rewrite <- H9.
apply H. exact IHx1. apply H7. exact H10. Save.
