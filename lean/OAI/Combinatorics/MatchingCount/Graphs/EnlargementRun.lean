import Mathlib
import OAI.Combinatorics.MatchingCount.Probability.Tv

namespace OAI

namespace MatchingFPRAS.Transport

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

noncomputable local instance : DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _

variable (hb : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hg : G.IsAcyclic)

omit [DecidableEq V] [DecidableEq J] in
lemma ladderLaw_pos (w : BagEdge bags → ℝ) (T q : ℕ)
    (s : Slot T q → PM (BagEdge.Incident (bags := bags))) : 0<ladderLaw w T q s := by
  apply prod_pos
  intro i _
  exact slotLaw_pos w i (s i)

lemma ladderWalk_nonneg (w : BagEdge bags → ℝ) (T q : ℕ)
    (z s : Slot T q → PM (BagEdge.Incident (bags := bags))) (t : ℕ) :
    0 ≤ FiniteChain.walk (ladderLaw w T q) (ladderFlow hb hg w T q) z t s := by
  apply FiniteChain.walk_nonneg _ (ladderLaw_pos w T q)
  exact scanFlow_nonneg (slotLaw w) (fun i a => (slotLaw_pos w i a).le)
    guides (base T q) (treeLadderCapacity hb hg w)

lemma ladderWalk_sum (w : BagEdge bags → ℝ) (T q : ℕ) (hq : 0<q)
    (z : Slot T q → PM (BagEdge.Incident (bags := bags))) (t : ℕ) :
    ∑ s,FiniteChain.walk (ladderLaw w T q) (ladderFlow hb hg w T q) z t s=1 := by
  apply FiniteChain.walk_sum _ (ladderLaw_pos w T q)
  intro s
  exact scanFlow_row (slotLaw w) (fun i => slotLaw_sum w i (z (topSlot T q hq)))
    guides (base T q) (Finset.card_pos.mp (by rwa [base_card])) (treeLadderCapacity hb hg w) s

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourcePM w K) := Classical.decEq _

lemma revealLaw_nonneg (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (p : SourcePM w K → ℝ) (hp : ∀ M,0≤p M) (a : SourceMarked w K) : 0≤revealLaw w K D p a := by
  apply Variation.sigmaLift_nonneg _ _ hp
  intro M a
  unfold Marking.conditional
  apply prod_nonneg
  intro e _
  apply div_nonneg (sourcePortions_nonneg w hw K D _ _)
  rw [sourcePortions_collapse]
  exact (sourceBagWeight_pos w hw K D hD e).le

lemma revealLaw_sum (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (p : SourcePM w K → ℝ) (hp : ∑ M,p M=1) : ∑ a,revealLaw w K D p a=1 := by
  apply Variation.sigmaLift_sum _ _ hp
  intro M
  apply Marking.conditional_sum
  intro e
  rw [sourcePortions_collapse]
  exact (sourceBagWeight_pos w hw K D hD e).ne'

noncomputable def sourceRun (w : V → V → ℝ) (K : ℕ)
    (hK : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K) (T q : ℕ) (hq : 0<q)
    (z : Slot T q → SourcePM w K) (t : ℕ) : SourceMarked w K → ℝ :=
  revealLaw w K (sourceD (V:=V) K)
    (Variation.push (FiniteChain.walk (ladderLaw (sourceBagWeight w K (sourceD (V:=V) K)) T q)
      (ladderFlow (fun x a ha b hb => sourceBag_tree_adjacent w K hK x a b ha hb)
        (sourceTree_isTree w K).2 (sourceBagWeight w K (sourceD (V:=V) K)) T q) z t)
      (fun a => a (topSlot T q hq)))

lemma sourceRun_nonneg (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (hK : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K) (T q : ℕ) (hq : 0<q)
    (z : Slot T q → SourcePM w K) (t : ℕ) (a : SourceMarked w K) :
    0 ≤ sourceRun w K hK T q hq z t a := by
  apply revealLaw_nonneg w hw K _ (sourceD_one K)
  intro M
  apply Variation.push_nonneg
  intro s
  exact ladderWalk_nonneg _ _ _ _ _ z s t

lemma sourceRun_sum (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (hK : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K) (T q : ℕ) (hq : 0<q)
    (z : Slot T q → SourcePM w K) (t : ℕ) : ∑ a,sourceRun w K hK T q hq z t a=1 := by
  apply revealLaw_sum w hw K _ (sourceD_one K)
  apply Variation.push_sum
  exact ladderWalk_sum _ _ _ _ _ hq z t

theorem sourceRun_tv (hn : 2 ≤ Fintype.card V)
    (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (hK : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K)
    (T : ℕ) (hT : max (sourceD (V:=V) K:ℝ) (3*4^K) ≤ (tierBase (SourceVertex V K))^T)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) (sourceD (V:=V) K))
    (z : Slot T (ladderQ (Fintype.card (SourceVertex V K)) (sourceD (V:=V) K)) → SourcePM w K)
    (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) :
    Variation.tv (sourceRun w K hK T _ hq z
      (ladderSteps (Fintype.card (SourceVertex V K)) (sourceD (V:=V) K) K T ξ))
      (sourceLaw w K (sourceD (V:=V) K)) ≤ ξ := by
  obtain ⟨hq',h⟩ := source_marked_sampling hn w hw K hK (z (topSlot T _ hq)) T hT z ξ hξ hξ1
  exact h

end MatchingFPRAS.Enlargement

namespace MatchingFPRAS.UnitRefresh

structure Pairing (α : Type*) where
  mate : α → α
  involutive : Function.Involutive mate
  no_fixed : ∀ x, mate x ≠ x

instance {α : Type*} [Finite α] : Finite (Pairing α) := by
  apply Finite.of_injective Pairing.mate
  intro p q h
  cases p; cases q
  simp only [Pairing.mk.injEq] at *
  exact h

noncomputable instance {α : Type*} [Fintype α] : Fintype (Pairing α) := Fintype.ofFinite _

@[ext] lemma Pairing.ext {α : Type*} {p q : Pairing α} (h : ∀ x, p.mate x=q.mate x) : p=q := by
  cases p; cases q
  simp only [Pairing.mk.injEq]
  exact funext h

variable {α β : Type*}

def Pairing.map (e : α ≃ β) (p : Pairing α) : Pairing β where
  mate y := e (p.mate (e.symm y))
  involutive y := by simp [p.involutive (e.symm y)]
  no_fixed y := by
    intro h
    apply p.no_fixed (e.symm y)
    have := congrArg e.symm h
    simpa using this

def Pairing.congr (e : α ≃ β) : Pairing α ≃ Pairing β where
  toFun := Pairing.map e
  invFun := Pairing.map e.symm
  left_inv p := by ext x; simp [Pairing.map]
  right_inv p := by ext x; simp [Pairing.map]

lemma Pairing.subtype_hext {P Q : α → Prop} (p : Pairing {x // P x}) (q : Pairing {x // Q x})
    (hPQ : ∀ x, P x ↔ Q x)
    (h : ∀ (x : {x // P x}) (y : {x // Q x}), x.val=y.val →
      (p.mate x).val=(q.mate y).val) : HEq p q := by
  have he : P=Q := funext fun x => propext (hPQ x)
  subst Q
  apply heq_of_eq
  ext x
  exact h x x rfl

variable [DecidableEq α]

def Pairing.remove (p : Pairing α) (a : α) : Pairing {x : α // x≠a ∧ x≠p.mate a} where
  mate x := ⟨p.mate x,by
    constructor
    · intro h
      have := congrArg p.mate h
      exact x.property.2 (by rw [p.involutive] at this; exact this)
    · intro h
      exact x.property.1 (p.involutive.injective h)⟩
  involutive x := Subtype.ext (p.involutive x)
  no_fixed x h := p.no_fixed x (congrArg Subtype.val h)

def Pairing.insert (a b : α) (hab : b≠a)
    (p : Pairing {x : α // x≠a ∧ x≠b}) : Pairing α where
  mate x := if hx : x=a then b else if hy : x=b then a else (p.mate ⟨x,hx,hy⟩).val
  involutive x := by
    by_cases hx : x=a
    · subst x; simp [hab]
    by_cases hy : x=b
    · subst x; simp [hab]
    simp only [dite_eq_right hx,dite_eq_right hy]
    rw [dite_eq_right (p.mate ⟨x,hx,hy⟩).property.1,dite_eq_right (p.mate ⟨x,hx,hy⟩).property.2]
    exact congrArg Subtype.val (p.involutive ⟨x,hx,hy⟩)
  no_fixed x := by
    by_cases hx : x=a
    · subst x; simpa using hab
    by_cases hy : x=b
    · subst x; simpa [hx] using hab.symm
    simp only [dite_eq_right hx,dite_eq_right hy]
    intro h
    exact p.no_fixed ⟨x,hx,hy⟩ (Subtype.ext h)

@[simp] lemma Pairing.insert_at (a b : α) (hab : b≠a)
    (p : Pairing {x : α // x≠a ∧ x≠b}) : (p.insert a b hab).mate a=b := by
  simp [Pairing.insert]

@[simp] lemma Pairing.insert_other (a b : α) (hab : b≠a)
    (p : Pairing {x : α // x≠a ∧ x≠b}) (x : {x : α // x≠a ∧ x≠b}) :
    (p.insert a b hab).mate x=(p.mate x).val := by
  simp [Pairing.insert,x.property.1,x.property.2]

noncomputable def Pairing.split (a : α) :
    Pairing α ≃ Σ b : {x : α // x≠a}, Pairing {x : α // x≠a ∧ x≠b.val} where
  toFun p := ⟨⟨p.mate a,p.no_fixed a⟩,p.remove a⟩
  invFun q := q.2.insert a q.1.val q.1.property
  left_inv p := by
    ext x
    by_cases hx : x=a
    · subst x; simp
    by_cases hy : x=p.mate a
    · subst x
      simp [Pairing.insert,p.no_fixed a,p.involutive a]
    · simp [Pairing.insert,hx,hy,Pairing.remove]
  right_inv q := by
    rcases q with ⟨⟨b,hb⟩,p⟩
    apply Sigma.ext (Subtype.ext (by simp))
    apply Pairing.subtype_hext
    · intro x; simp only [Pairing.insert_at]
    · intro x y hxy
      change (p.insert a b hb).mate x = (p.mate y).val
      rw [hxy]
      exact Pairing.insert_other a b hb p y

def pairingCount : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n+2 => (n+1)*pairingCount n

@[simp] lemma pairingCount_zero : pairingCount 0=1 := rfl

@[simp] lemma pairingCount_one : pairingCount 1=0 := rfl

@[simp] lemma pairingCount_add_two (n : ℕ) : pairingCount (n+2)=(n+1)*pairingCount n := rfl

lemma pairingCount_pos_recurrence {n : ℕ} (hn : 0<n) :
    pairingCount n = (n-1)*pairingCount (n-2) := by
  match n with
  | 0 => omega
  | 1 => rfl
  | n+2 => simp only [pairingCount_add_two,Nat.add_sub_cancel,show n+2-1=n+1 by omega]

lemma card_except_two [Fintype α] (a b : α) (hab : b≠a) :
    Fintype.card {x : α // x≠a ∧ x≠b}=Fintype.card α-2 := by
  classical
  calc
    _ = Fintype.card {x : α // ¬ (x=a ∨ x=b)} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun x => not_or.symm)
    _ = Fintype.card α-Fintype.card {x : α // x=a ∨ x=b} := Fintype.card_subtype_compl _
    _ = _ := by rw [Fintype.card_subtype_eq_or_eq_of_ne hab.symm]

universe u

private theorem pairing_card_aux (n : ℕ) : ∀ (α : Type u) [Fintype α],
    Fintype.card α=n → Fintype.card (Pairing α)=pairingCount n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro α inst hcard
    classical
    by_cases hn : n=0
    · have hzero : Fintype.card α=0 := hcard.trans hn
      let : IsEmpty α := Fintype.card_eq_zero_iff.mp hzero
      let p : Pairing α := ⟨id,fun x => rfl,fun x => isEmptyElim x⟩
      let : Unique (Pairing α) := ⟨⟨p⟩,fun q => by ext x; exact isEmptyElim x⟩
      simp [hn]
    · have hnpos : 0<n := Nat.pos_of_ne_zero hn
      have hα : Nonempty α := Fintype.card_pos_iff.mp (by omega)
      let a : α := Classical.choice hα
      have hm : n-2<n := Nat.sub_lt hnpos (by omega)
      have he (b : {x : α // x≠a}) :
          Fintype.card (Pairing {x : α // x≠a ∧ x≠b.val})=pairingCount (n-2) := by
        apply ih (n-2) hm
        rw [card_except_two a b.val b.property,hcard]
      calc
        _ = Fintype.card (Σ b : {x : α // x≠a}, Pairing {x : α // x≠a ∧ x≠b.val}) :=
          Fintype.card_congr (Pairing.split a)
        _ = ∑ b : {x : α // x≠a}, Fintype.card (Pairing {x : α // x≠a ∧ x≠b.val}) :=
          Fintype.card_sigma
        _ = ∑ _b : {x : α // x≠a}, pairingCount (n-2) := Finset.sum_congr rfl (fun b _ => he b)
        _ = (n-1)*pairingCount (n-2) := by
          simp [Fintype.card_subtype_compl,hcard]
        _ = pairingCount n := (pairingCount_pos_recurrence hnpos).symm

omit [DecidableEq α] in
theorem pairing_card [Fintype α] : Fintype.card (Pairing α)=pairingCount (Fintype.card α) :=
  pairing_card_aux (Fintype.card α) α rfl

end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.Initializer

open Finset MatchingFPRAS.Switching MatchingFPRAS.UnitRefresh

variable {V : Type*} [Fintype V] [LinearOrder V]

noncomputable def restrictHoles (R : Finset V) (m : {m : Mate V // HasHoles m R}) :
    Pairing {x : V // x∉R} where
  mate x := ⟨m.val.val x.val,fun h => x.property ((mate_mem_holes_iff m.val R m.property x.val).mp h)⟩
  involutive x := Subtype.ext (m.val.property x.val)
  no_fixed x h := x.property ((m.property x.val).mp (congrArg Subtype.val h))

noncomputable def fillFixed (R : Finset V) (p : Pairing {x : V // x∉R}) : Mate V := by
  classical
  refine ⟨fun x => if hx : x∉R then (p.mate ⟨x,hx⟩).val else x,?_⟩
  intro x
  by_cases hx : x∉R
  · simp only [dite_eq_left hx]
    rw [dite_eq_left (p.mate ⟨x,hx⟩).property]
    exact congrArg Subtype.val (p.involutive ⟨x,hx⟩)
  · simp only [dite_eq_right hx]

omit [Fintype V] in
lemma fillFixed_holes (R : Finset V) (p : Pairing {x : V // x∉R}) : HasHoles (fillFixed R p) R := by
  classical
  intro x
  by_cases hx : x∉R
  · simp only [fillFixed,iff_false,hx]
    intro h
    exact p.no_fixed ⟨x,hx⟩ (Subtype.ext h)
  · simp only [fillFixed,dite_eq_right hx]
    exact iff_of_true trivial (not_not.mp hx)

noncomputable def holesPairingEquiv (R : Finset V) :
    {m : Mate V // HasHoles m R} ≃ Pairing {x : V // x∉R} where
  toFun := restrictHoles R
  invFun p := ⟨fillFixed R p,fillFixed_holes R p⟩
  left_inv m := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    by_cases hx : x∉R
    · change (if hy : x∉R then (restrictHoles R m).mate ⟨x,hy⟩ |>.val else x)=m.val.val x
      rw [dite_eq_left hx]
      rfl
    · change (if hy : x∉R then (restrictHoles R m).mate ⟨x,hy⟩ |>.val else x)=m.val.val x
      rw [dite_eq_right hx]
      exact ((m.property x).mpr (not_not.mp hx)).symm
  right_inv p := by
    apply Pairing.ext
    intro x
    apply Subtype.ext
    change (fillFixed R p).val x.val=(p.mate x).val
    simp only [fillFixed,dite_eq_left x.property]

lemma matchings_card (R : Finset V) :
    (matchings R).card=pairingCount (Fintype.card V-R.card) := by
  classical
  calc
    _ = Fintype.card {m : Mate V // HasHoles m R} := by
      rw [Fintype.card_subtype]
      apply congrArg Finset.card
      ext m
      simp [matchings]
    _ = Fintype.card (Pairing {x : V // x∉R}) := Fintype.card_congr (holesPairingEquiv R)
    _ = _ := by rw [pairing_card,Fintype.card_subtype_compl,Fintype.card_coe]

lemma uniform_weight (c : ℝ) (R : Finset V) (m : Mate V) (hm : HasHoles m R) :
    weight (fun _ _ => c) m=c^((Fintype.card V-R.card)/2) := by
  classical
  have hmc : HasHoles m Rᶜᶜ := by simpa using hm
  have hc := mate_edge_count m Rᶜ hmc
  rw [Finset.card_compl] at hc
  have he : (univ.filter fun v => v < m.val v).card=(Fintype.card V-R.card)/2 := by omega
  unfold weight
  rw [←Finset.prod_filter (s:=univ) (fun v : V => v < m.val v) (fun _ : V => c)]
  simp only [Finset.prod_const,he]

theorem uniform_partition (c : ℝ) (R : Finset V) :
    partition (fun _ _ : V => c) R=
      (pairingCount (Fintype.card V-R.card):ℝ)*c^((Fintype.card V-R.card)/2) := by
  unfold partition
  simp_rw [Finset.sum_congr rfl (fun m hm => uniform_weight c R m ((mem_matchings m R).mp hm))]
  simp only [Finset.sum_const,nsmul_eq_mul,matchings_card]

lemma pairingCount_pos_of_even (n : ℕ) (h : Even n) : 0 < pairingCount n := by
  obtain ⟨k,rfl⟩ := h
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k+1+(k+1)=(k+k)+2 by omega,pairingCount_add_two]
    exact Nat.mul_pos (by omega) ih

lemma uniform_hole_ratio (hn : 2 ≤ Fintype.card V) (he : Even (Fintype.card V))
    (c : ℝ) (hc : 0 < c) (a b : V) (hab : a≠b) :
    holeRatio (fun _ _ : V => c) {a,b}=1/((Fintype.card V-1)*c) := by
  have h2 : ({a,b} : Finset V).card=2 := by simp [hab]
  have hc2 : Fintype.card V-2+2=Fintype.card V := by omega
  have he2 : Even (Fintype.card V-2) := by obtain ⟨k,hk⟩ := he; exact ⟨k-1,by omega⟩
  have hp : (pairingCount (Fintype.card V-2):ℝ)≠0 := by
    exact_mod_cast (pairingCount_pos_of_even _ he2).ne'
  have hpow : c^((Fintype.card V-2)/2)≠0 := pow_ne_zero _ hc.ne'
  unfold holeRatio
  rw [uniform_partition,uniform_partition,h2,Finset.card_empty,Nat.sub_zero]
  have hnrec : pairingCount (Fintype.card V)=
      (Fintype.card V-1)*pairingCount (Fintype.card V-2) :=
    pairingCount_pos_recurrence (by omega)
  have hexp : Fintype.card V/2=(Fintype.card V-2)/2+1 := by omega
  rw [hnrec,hexp,pow_succ,Nat.cast_mul,Nat.cast_sub (by omega : 1≤Fintype.card V),Nat.cast_one]
  field_simp

def initialScale (n : ℕ) : ℚ := 1/(Nat.sqrt (n-1):ℚ)

lemma sqrt_square_bounds (n : ℕ) (hn : 2 ≤ n) :
    (n-1:ℝ)/4 ≤ (Nat.sqrt (n-1):ℝ)^2 ∧ (Nat.sqrt (n-1):ℝ)^2 ≤ n-1 := by
  have hpos : 1 ≤ Nat.sqrt (n-1) := Nat.le_sqrt.mpr (by omega)
  have hlow := Nat.lt_succ_sqrt' (n-1)
  have hup := Nat.sqrt_le' (n-1)
  have hncast : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
  have hlow' : (n:ℝ)-1 < ((Nat.sqrt (n-1):ℝ)+1)^2 := by
    rw [←hncast]
    exact_mod_cast hlow
  have hup' : (Nat.sqrt (n-1):ℝ)^2 ≤ (n:ℝ)-1 := by
    rw [←hncast]
    exact_mod_cast hup
  have hs : (1:ℝ) ≤ Nat.sqrt (n-1) := by exact_mod_cast hpos
  constructor
  · nlinarith [sq_nonneg ((Nat.sqrt (n-1):ℝ)-1)]
  · exact hup'

lemma initialScale_pos (n : ℕ) (hn : 2 ≤ n) : 0 < initialScale n := by
  unfold initialScale
  have hs : 0 < Nat.sqrt (n-1) := by have := Nat.le_sqrt.mpr (by omega : 1*1≤n-1); omega
  positivity

theorem initial_balanced (hn : 2 ≤ Fintype.card V) (he : Even (Fintype.card V)) :
    let w := fun _ _ : V => ((initialScale (Fintype.card V):ℚ):ℝ)^2
    (0 < partition w ∅) ∧
    (∀ a,(1:ℝ)/4 ≤ rowMax hn w a) ∧ (∀ a,rowMax hn w a ≤ 1) := by
  dsimp only
  let n := Fintype.card V
  have hs : 0 < ((initialScale n:ℚ):ℝ) := by exact_mod_cast initialScale_pos n hn
  have hsq : 0 < ((initialScale n:ℚ):ℝ)^2 := sq_pos_of_pos hs
  have hr (a b : V) (hab : a≠b) :
      holeRatio (fun _ _ : V => ((initialScale n:ℚ):ℝ)^2) {a,b}=
        (Nat.sqrt (n-1):ℝ)^2/(n-1) := by
    rw [uniform_hole_ratio hn he _ hsq a b hab]
    unfold initialScale
    push_cast
    change 1/((n-1)*((1:ℝ)/Nat.sqrt (n-1))^2)=_
    have hp : (Nat.sqrt (n-1):ℝ)≠0 := by
      have h := initialScale_pos n hn
      simp only [initialScale,one_div,inv_pos] at h
      exact_mod_cast h.ne'
    field_simp
  have hnreal : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0:ℝ) < n-1 := by linarith
  refine ⟨?_,?_,?_⟩
  · rw [uniform_partition,Finset.card_empty,Nat.sub_zero]
    exact mul_pos (by exact_mod_cast pairingCount_pos_of_even n he) (pow_pos hsq _)
  · intro a
    obtain ⟨b,hba,hb⟩ := rowMax_attained hn (fun _ _ : V => ((initialScale n:ℚ):ℝ)^2) a
    rw [←hb,hr a b hba.symm]
    have hbnd := (sqrt_square_bounds n hn).1
    apply (le_div_iff₀ hden).mpr
    linarith
  · intro a
    obtain ⟨b,hba,hb⟩ := rowMax_attained hn (fun _ _ : V => ((initialScale n:ℚ):ℝ)^2) a
    rw [←hb,hr a b hba.symm]
    exact (div_le_one hden).mpr
      (sqrt_square_bounds n hn).2

end MatchingFPRAS.Initializer

end OAI
