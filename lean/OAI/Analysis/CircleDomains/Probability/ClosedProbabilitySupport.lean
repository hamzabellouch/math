import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Semicontinuity.Basic

namespace OAI

/-! Support in a closed set is retained by weak limits of probability laws. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma isClosed_probability_supported_closed
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] {F : Set X} (hF : IsClosed F) :
    IsClosed {P : ProbabilityMeasure X | ∀ᵐ x ∂(P : Measure X), x ∈ F} := by
  have hsc : UpperSemicontinuous (fun P : ProbabilityMeasure X => (P : Measure X) F) :=
    upperSemicontinuous_iff_limsup_le.mpr (fun P =>
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto tendsto_id hF)
  have he : {P : ProbabilityMeasure X | ∀ᵐ x ∂(P : Measure X), x ∈ F} =
      {P : ProbabilityMeasure X | (1 : ℝ≥0∞) ≤ (P : Measure X) F} := by
    ext P
    change (∀ᵐ x ∂(P : Measure X), x ∈ F) ↔ (1 : ℝ≥0∞) ≤ (P : Measure X) F
    constructor
    · intro h
      have heq : F =ᵐ[(P : Measure X)] univ := h.mono (fun x hx => by simp [hx])
      rw [measure_congr heq,measure_univ]
    · intro h
      have hm : (P : Measure X) F = 1 := le_antisymm ((measure_mono (subset_univ F)).trans_eq measure_univ) h
      have hc : (P : Measure X) Fᶜ = 0 := by
        rw [measure_compl hF.measurableSet (measure_ne_top _ _),hm,measure_univ,tsub_self]
      apply ae_iff.mpr
      change (P : Measure X) Fᶜ = 0
      exact hc
  rw [he]
  exact hsc.isClosed_preimage 1

lemma probability_supported_closed_of_tendsto
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] {P : ℕ → ProbabilityMeasure X} {Q : ProbabilityMeasure X}
    (hlim : Tendsto P atTop (𝓝 Q)) {F : Set X} (hF : IsClosed F)
    (hsupp : ∀ᶠ n in atTop, ∀ᵐ x ∂(P n : Measure X), x ∈ F) :
    ∀ᵐ x ∂(Q : Measure X), x ∈ F :=
  (isClosed_probability_supported_closed hF).mem_of_tendsto hlim hsupp

end CircleDomainRigidity

end

end OAI
