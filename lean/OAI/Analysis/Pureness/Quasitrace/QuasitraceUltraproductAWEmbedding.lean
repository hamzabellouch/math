import Mathlib.RingTheory.Congruence.Hom
import OAI.Analysis.Pureness.Quasitrace.QuasitraceUltralimitPositive
import OAI.Analysis.Pureness.States.QuotientGenuineQuasitrace
import OAI.Analysis.Pureness.States.QuotientAWStar
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientFinite

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {ι : Type*} [Nonempty ι] {D : ι → Type*}
variable [∀ i, CStarAlgebra (D i)] [∀ i, PartialOrder (D i)]
  [∀ i, StarOrderedRing (D i)] [∀ i, Nontrivial (D i)]

instance boundedProductNontrivial : Nontrivial (lp D ∞) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  apply nontrivial_of_ne (1 : lp D ∞) 0
  intro h
  exact one_ne_zero (congrArg (fun u : lp D ∞ => u i) h)

variable (T : ∀ i, PositiveQuasitrace (D i)) (U : Ultrafilter ι)
variable (hunit : ∀ i, T i ⟨1, zero_le_one⟩ = 1)
variable (hadd : ∀ i (x y : D i), (T i).metricSize (x+y) ≤ (T i).metricSize x+(T i).metricSize y)
variable (hsqrt : ∀ i (a b : Positive (D i)), Real.sqrt (T i (Positive.add a b)) ≤
      Real.sqrt (T i a)+Real.sqrt (T i b))

abbrev UltralimitAWCompletion :=
  (ultralimitPositiveQuasitrace T U hunit).CauchyQuotient
    (ultralimitPositiveQuasitrace_metricSize_add T U hunit hadd)

def ultralimitCompletionMap : lp D ∞ →⋆ₐ[ℂ] UltralimitAWCompletion T U hunit hadd :=
  (ultralimitPositiveQuasitrace T U hunit).quotientEmbedding
    (ultralimitPositiveQuasitrace_metricSize_add T U hunit hadd)

lemma ultralimitCompletionMap_eq (u v : lp D ∞) :
    ultralimitCompletionMap T U hunit hadd u = ultralimitCompletionMap T U hunit hadd v ↔
      (filteredQuasitraceNullIdeal T (U : Filter ι) hadd).ringCon u v := by
  let P := ultralimitPositiveQuasitrace T U hunit
  let ha := ultralimitPositiveQuasitrace_metricSize_add T U hunit hadd
  rw [TwoSidedIdeal.rel_iff, ← quasitraceUltraSize_eq_zero T U hunit hadd]
  rw [← ultralimitPositiveQuasitrace_metricSize T U hunit]
  change P.quotientEmbedding ha u = P.quotientEmbedding ha v ↔ P.metricSize (u-v) = 0
  constructor
  · intro h
    have hc : (P.nullSequenceIdeal ha).ringCon (P.constantCauchy ha u) (P.constantCauchy ha v) :=
      Quotient.exact h
    rw [P.nullSequenceIdeal_rel ha] at hc
    change Tendsto (fun _ : ℕ => P.metricSize (u-v)) atTop (nhds 0) at hc
    exact tendsto_nhds_unique tendsto_const_nhds hc
  · intro h
    apply Quotient.sound
    change (P.nullSequenceIdeal ha).ringCon (P.constantCauchy ha u) (P.constantCauchy ha v)
    rw [P.nullSequenceIdeal_rel ha]
    change Tendsto (fun _ : ℕ => P.metricSize (u-v)) atTop (nhds 0)
    rw [h]
    exact tendsto_const_nhds

def ultraproductAWEmbedding :
    FilteredQuasitraceQuotient T (U : Filter ι) hadd hunit →⋆ₐ[ℂ]
      UltralimitAWCompletion T U hunit hadd :=
  { (filteredQuasitraceNullIdeal T (U : Filter ι) hadd).ringCon.liftₐ
      (ultralimitCompletionMap T U hunit hadd).toAlgHom
      (fun u v h => (ultralimitCompletionMap_eq T U hunit hadd u v).mpr h) with
    map_star' := by
      intro x
      obtain ⟨u,rfl⟩ := (filteredQuasitraceClosedIdeal T (U : Filter ι) hadd hunit).quotientMap_surjective x
      exact map_star (ultralimitCompletionMap T U hunit hadd) u }

lemma ultraproductAWEmbedding_map (u : lp D ∞) :
    ultraproductAWEmbedding T U hunit hadd
      (filteredQuasitraceQuotientMap T (U : Filter ι) hadd hunit u) =
        ultralimitCompletionMap T U hunit hadd u := rfl

lemma ultraproductAWEmbedding_injective : Function.Injective (ultraproductAWEmbedding T U hunit hadd) := by
  intro x y h
  obtain ⟨u,rfl⟩ := (filteredQuasitraceClosedIdeal T (U : Filter ι) hadd hunit).quotientMap_surjective x
  obtain ⟨v,rfl⟩ := (filteredQuasitraceClosedIdeal T (U : Filter ι) hadd hunit).quotientMap_surjective y
  apply Quotient.sound
  exact (ultralimitCompletionMap_eq T U hunit hadd u v).mp h

include hsqrt in
theorem ultralimitAWCompletion_annihilator (S : Set (UltralimitAWCompletion T U hunit hadd)) :
    ∃ p : UltralimitAWCompletion T U hunit hadd, IsStarProjection p ∧
      ∀ z, (∀ a ∈ S, a*z=0) ↔ p*z=z :=
  PositiveQuasitrace.quotient_right_annihilator_projection _ _
    (ultralimitPositiveQuasitrace_sqrt_add T U hunit hsqrt) S

include hsqrt in
theorem ultralimitAWCompletion_finite (x : UltralimitAWCompletion T U hunit hadd)
    (hx : star x*x=1) : x*star x=1 :=
  PositiveQuasitrace.cauchyQuotient_isometry_unitary _ _
    (ultralimitPositiveQuasitrace_sqrt_add T U hunit hsqrt) x hx

include hsqrt in
theorem filteredQuasitraceQuotient_finite
    (x : FilteredQuasitraceQuotient T (U : Filter ι) hadd hunit) (hx : star x*x=1) : x*star x=1 := by
  apply ultraproductAWEmbedding_injective T U hunit hadd
  rw [map_one,map_mul,map_star]
  apply ultralimitAWCompletion_finite T U hunit hadd hsqrt
  rw [← map_star,← map_mul,hx,map_one]

def ultralimitAWQuasitrace : ComplexQuasitrace (UltralimitAWCompletion T U hunit hadd) :=
  (ultralimitPositiveQuasitrace T U hunit).quotientComplexQuasitrace
    (ultralimitPositiveQuasitrace_metricSize_add T U hunit hadd)
    (ultralimitPositiveQuasitrace_sqrt_add T U hunit hsqrt)

lemma ultralimitAWQuasitrace_original (u : lp D ∞) :
    ultralimitAWQuasitrace T U hunit hadd hsqrt (ultralimitCompletionMap T U hunit hadd u) =
      (ultralimitPositiveQuasitrace T U hunit).complexValue u := by
  rw [ultralimitAWQuasitrace,PositiveQuasitrace.quotientComplexQuasitrace_eq]
  exact PositiveQuasitrace.quotientValue_embedding _ _ _ u

lemma ultralimitAWQuasitrace_faithful (x : UltralimitAWCompletion T U hunit hadd) :
    ultralimitAWQuasitrace T U hunit hadd hsqrt (star x*x)=0 ↔ x=0 := by
  rw [ultralimitAWQuasitrace,PositiveQuasitrace.quotientComplexQuasitrace_eq]
  exact PositiveQuasitrace.quotientValue_square_eq_zero_iff _ _ _ x

lemma ultralimitAWQuasitrace_unit : ultralimitAWQuasitrace T U hunit hadd hsqrt 1 = 1 := by
  have h := ultralimitAWQuasitrace_original T U hunit hadd hsqrt (1 : lp D ∞)
  rw [map_one] at h
  rw [h,PositiveQuasitrace.complexValue_positive (a := ⟨1,zero_le_one⟩)]
  change (quasitraceUltraPositive T U ⟨1,zero_le_one⟩ : ℂ) = 1
  rw [quasitraceUltraPositive_one T U hunit,Complex.ofReal_one]
end CuntzPureness

end

end OAI
