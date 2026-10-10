import Mathlib
import OAI.Combinatorics.MatchingCount.Probability.AdaptiveLaw
import OAI.Combinatorics.MatchingCount.Graphs.LabelOrder
import OAI.Combinatorics.MatchingCount.Sampling.TableMarking

namespace OAI

namespace MatchingFPRAS.Variation
lemma imageLaw_instances {A B : Type*} (F₁ F₂ : Fintype A) (f : A → B) :
    @imageLaw A B F₁ f=@imageLaw A B F₂ f := by
  cases Subsingleton.elim F₁ F₂
  rfl
lemma tv_instances {A : Type*} (F₁ F₂ : Fintype A) (p q : A → ℝ) :
    @tv A F₁ p q=@tv A F₂ p q := by
  cases Subsingleton.elim F₁ F₂
  rfl
end MatchingFPRAS.Variation
namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : V → V → ℚ) (K : ℕ) : DecidableEq (BagPM (bags w K)) := Classical.decEq _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) : Fintype (BagPM (bags w K)) := Fintype.ofFinite _

def centralEdge (w : V → V → ℚ) (K : ℕ) (e : LogicalEdge V) : BagEdge (bags w K) :=
  coloredReal w K (e,⟨2*(2*K+2),by omega⟩)
def probePortion (w : V → V → ℚ) (K D : ℕ) (e : BagEdge (bags w K)) : ℚ :=
  if ∃ q,centralEdge w K q=e then 1/(D:ℚ) else 0
def portions (w : V → V → ℚ) (K D : ℕ) (e : BagEdge (bags w K)) : Fin 3 → ℚ :=
  ![realPortion w K e,bagHeight w K e.color/D-probePortion w K D e,probePortion w K D e]
lemma portions_sum (w : V → V → ℚ) (K D : ℕ) (e : BagEdge (bags w K)) :
    ∑ i,portions w K D e i=bagWeight w K D e := by
  simp [portions,Fin.sum_univ_succ,bagWeight]
lemma portions_nonneg (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ)
    (e : BagEdge (bags w K)) (i : Fin 3) : 0≤portions w K D e i := by
  fin_cases i
  · exact realPortion_nonneg w hw K e
  · change 0≤bagHeight w K e.color/D-probePortion w K D e
    apply sub_nonneg.mpr
    unfold probePortion
    split_ifs
    · exact div_le_div_of_nonneg_right (bagHeight_one w K _) (Nat.cast_nonneg D)
    · exact div_nonneg (by dsimp [bagHeight]; positivity) (Nat.cast_nonneg D)
  · change 0≤probePortion w K D e
    unfold probePortion
    split_ifs <;> positivity
lemma bagWeight_pos (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (e : BagEdge (bags w K)) : 0<bagWeight w K D e := by
  apply add_pos_of_nonneg_of_pos (realPortion_nonneg w hw K e)
  exact div_pos (by dsimp [bagHeight]; positivity) (by exact_mod_cast hD)

def markingTable (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (e : BagEdge (bags w K)) : WeightedOptions (Fin 3) where
  size:=3
  out:=id
  mass i:=portions w K D e i/bagWeight w K D e
  nonneg i:=div_nonneg (portions_nonneg w hw K D e i) (bagWeight_pos w hw K D hD e).le
  total:=by rw [←sum_div,portions_sum,div_self (bagWeight_pos w hw K D hD e).ne']
lemma markingTable_law (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (e : BagEdge (bags w K)) (i : Fin 3) :
    (markingTable w hw K D hD e).law i=portions w K D e i/bagWeight w K D e := by
  change (∑ j : Fin 3,if j=i then portions w K D e j/bagWeight w K D e else 0)=_
  simp only [sum_ite_eq',mem_univ,ite_true]

abbrev Marked (w : V → V → ℚ) (K : ℕ) := TableMarking.Marked (I:=Fin 3) (BagEdge.Incident (bags:=bags w K))
noncomputable local instance sourceMarkedFintype (w : V → V → ℚ) (K : ℕ) :
    Fintype (Marked w K) := Fintype.ofFinite _
noncomputable def markedLaw (w : V → V → ℚ) (K D : ℕ) : Marked w K → ℝ :=
  sigmaLift (gibbs (fun e=>(bagWeight w K D e:ℝ)))
    (fun M=>product (fun e : M.val=>fun i=>(portions w K D e.val i/bagWeight w K D e.val:ℚ)))

def markedSampler (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<Transport.ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :=
  TableMarking.draw BagEdge.Incident (topSampler w K D m hN h hq M η)
    (markingTable w hw K D hD)
    (bitPrecision (6*Fintype.card (BagEdge (bags w K))) η)

noncomputable local instance sourceMarkingBitsFintype {A : Type*} [Fintype A]
    (w : V → V → ℚ) (K k : ℕ) :
    Fintype (A × (BagEdge (bags w K) → Fin k → Bool)) := Fintype.ofFinite _

lemma marking_tv {A : Type*} [Fintype A] [Nonempty A]
    (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (f : A → BagPM (bags w K)) (k : ℕ) :
    tv (imageLaw (TableMarking.draw BagEdge.Incident f (markingTable w hw K D hD) k))
      (markedLaw w K D)≤tv (imageLaw f) (gibbs (fun e=>(bagWeight w K D e:ℝ)))+
        6*Fintype.card (BagEdge (bags w K))/(2:ℝ)^k := by
  have he : TableMarking.law BagEdge.Incident (fun e=>(bagWeight w K D e:ℝ))
      (markingTable w hw K D hD)=markedLaw w K D := by
    unfold TableMarking.law TableMarking.portion markedLaw
    simp only [markingTable_law]
  have hh:=TableMarking.draw_tv_size BagEdge.Incident f
    (fun e=>(bagWeight w K D e:ℝ)) (markingTable w hw K D hD) k 3 (fun _=>rfl)
  rw [he] at hh
  norm_num only [Nat.cast_ofNat] at hh
  rw [imageLaw_instances _ (sourceMarkingBitsFintype w K k),
    tv_instances _ (sourceMarkedFintype w K)] at hh
  exact hh

noncomputable def markedSamplerLaw (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<Transport.ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    Marked w K → ℝ := imageLaw (markedSampler w hw K D m hD hN h hq M η)

theorem markedSampler_tv (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ) (hD : 1≤D)
    (hN : 2≤Fintype.card (SourceVertex V K)) (hm : 1 < m)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<Transport.ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) (hη : 0<η) :
    tv (markedSamplerLaw w hw K D m (lt_of_lt_of_le Nat.zero_lt_one hD) (lt_of_lt_of_le Nat.zero_lt_two hN) h hq M η)
      (markedLaw w K D)≤2*(η:ℝ)+(m:ℝ)⁻¹ := by
  have hh:=marking_tv w hw K D (lt_of_lt_of_le Nat.zero_lt_one hD)
    (topSampler w K D m (lt_of_lt_of_le Nat.zero_lt_two hN) h hq M η)
    (bitPrecision (6*Fintype.card (BagEdge (bags w K))) η)
  have hs:=topSampler_tv w hw K D m hD hN hm h hq M η hη
  have hb:=bitPrecision_error (6*Fintype.card (BagEdge (bags w K))) η hη
  push_cast at hb
  change tv (markedSamplerLaw w hw K D m (lt_of_lt_of_le Nat.zero_lt_one hD)
    (lt_of_lt_of_le Nat.zero_lt_two hN) h hq M η) _≤_ at hh
  linarith
end MatchingFPRAS.RationalSource

end OAI
