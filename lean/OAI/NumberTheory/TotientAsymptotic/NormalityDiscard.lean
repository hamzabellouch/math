import OAI.NumberTheory.TotientAsymptotic.NormalInternalDiscard
import OAI.NumberTheory.TotientAsymptotic.NormalHeadDiscard

namespace OAI

/-! The complete normality exclusion for the actual universally good tuples. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def nonNormalInternalTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η ∈ nonNormalInternalRemainders x H,
    prefixOfRemainder x H η=τ.tail)

def FailsWitnessNormality {x : ℝ} {H : ℕ} (p : ℕ) (η : RemainderDatum (L x H)) : Prop :=
  ∃ i ∈ Finset.Icc 0 (R x H), ∃ j ∈ Finset.Icc i (collisionLastIndex x i),
    ¬IsNormalPrime (normalityScale x i) (wholeWitnessPrime p η j)

def normalityFailureTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η : RemainderDatum (L x H),
    IsBasicRemainder x H η ∧ prefixOfRemainder x H η=τ.tail ∧ FailsWitnessNormality τ.head η)

lemma nonNormalInternalRemainders_basic {x : ℝ} {H : ℕ}
    {η : RemainderDatum (L x H)} (hη : η ∈ nonNormalInternalRemainders x H) :
    IsBasicRemainder x H η := by
  obtain ⟨i,_,hj⟩ := Finset.mem_biUnion.mp hη
  obtain ⟨j,_,hη⟩ := Finset.mem_biUnion.mp hj
  exact mem_basicRemainderFinset.mp (Finset.mem_filter.mp hη).1

lemma nonNormalInternalTuples_card_le {x t : ℝ} {H : ℕ} (hPH : P H ≤ H) :
    (nonNormalInternalTuples x H t).card ≤
      (witnessFamily t (nonNormalInternalRemainders x H)).card := by
  have hsub : nonNormalInternalTuples x H t ⊆
      (witnessFamily t (nonNormalInternalRemainders x H)).image (fun q => witnessTuple q.2 q.1) := by
    intro τ hτ
    obtain ⟨hτ,η,hη,he⟩ := Finset.mem_filter.mp hτ
    have hb := (mem_tupleFinset hPH).mp hτ
    have hw : witnessTuple τ.head η=τ := by
      cases τ
      simpa only [witnessTuple,TotientTuple.mk.injEq,true_and] using he
    refine Finset.mem_image.mpr ⟨(η,τ.head),?_,hw⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hη,Finset.mem_range.mpr (basic_tuple_head_bound hPH hb)⟩,?_⟩
    exact hw.symm ▸ hb
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

lemma normalityFailureTuples_subset {x t : ℝ} {H : ℕ}
    (hind : ∀ i ≤ R x H, collisionLastIndex x i < L x H) :
    normalityFailureTuples x H t ⊆ nonNormalHeadTuples x H t ∪ nonNormalInternalTuples x H t := by
  intro τ hτ
  obtain ⟨ht,η,hη,he,i,hi,j,hj,hn⟩ := Finset.mem_filter.mp hτ
  obtain ⟨hji,hjk⟩ := Finset.mem_Icc.mp hj
  by_cases hj0 : j=0
  · have hi0 : i=0 := by omega
    subst i
    subst j
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht,by simpa [wholeWitnessPrime] using hn⟩)
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨ht,η,?_,he⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨i,hi,Finset.mem_biUnion.mpr ⟨j,?_,?_⟩⟩
    · exact Finset.mem_Icc.mpr ⟨max_le (by omega) hji,hjk.trans (hind i (Finset.mem_Icc.mp hi).2).le⟩
    · exact Finset.mem_filter.mpr ⟨mem_basicRemainderFinset.mpr hη,by
        simpa only [wholeWitnessPrime,ite_eq_right hj0] using hn⟩

/-- Normality is required for every full basic witness, including alternate
witnesses of the same tuple. The whole excluded tuple family is negligible. -/
theorem normality_tuple_discard (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) (hford : FordLemma26Input) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
        ((normalityFailureTuples x H t).card : ℝ) ≤ ε H*(x/Real.log x*G x (m x)) := by
  obtain ⟨δ,hδ,hsmall⟩ := normal_internal_reciprocal_discard hbox hren hmertens hford
  obtain ⟨γ,hγ,hhead⟩ := normal_head_tuple_discard hbox hren hmertens hford
  refine ⟨fun H => γ H+10*δ H,by simpa using hγ.add (hδ.const_mul 10),?_⟩
  filter_upwards [hsmall,hhead,eventually_collision_indices,eventually_ge_atTop 2]
    with H hH hh hind hH2
  filter_upwards [hH,hh,restricted_witness_count,m_tendsto.eventually (eventually_ge_atTop H),
    eventually_gt_atTop (1 : ℝ)] with x hx hh hc hm hx1
  intro t ht
  have hPH := (P_lt_self hH2).le
  have hcoef : 0 ≤ 10*x/Real.log x := div_nonneg (by linarith) (Real.log_pos hx1).le
  have hi : ((nonNormalInternalTuples x H t).card : ℝ) ≤ 10*δ H*(x/Real.log x*G x (m x)) := by
    calc
      _ ≤ ((witnessFamily t (nonNormalInternalRemainders x H)).card : ℝ) :=
        Nat.cast_le.mpr (nonNormalInternalTuples_card_le hPH)
      _ ≤ (10*x/Real.log x)*(∑ η ∈ nonNormalInternalRemainders x H, remainderReciprocalWeight η) :=
        hc H hPH t ht _ (fun _ hη => nonNormalInternalRemainders_basic hη)
      _ ≤ (10*x/Real.log x)*(δ H*G x (m x)) := mul_le_mul_of_nonneg_left hx hcoef
      _ = _ := by ring
  have hcard := (Finset.card_le_card (normalityFailureTuples_subset (x := x) (t := t) (H := H)
    (fun i hi => (hind x hm i hi).2.2))).trans (Finset.card_union_le _ _)
  have hcardR : ((normalityFailureTuples x H t).card : ℝ) ≤
      (nonNormalHeadTuples x H t).card+(nonNormalInternalTuples x H t).card := by exact_mod_cast hcard
  exact hcardR.trans ((add_le_add (hh t ht) hi).trans_eq (by ring))

end TotientAsymptotic

end

end OAI
