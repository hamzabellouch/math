import OAI.Analysis.CircleDomains.Sobolev.WeakProbabilityMeasurability
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Laws supported on a G-delta form a G-delta in the weak topology.
Closed-set evaluation is upper semicontinuous by portmanteau. -/
open Set Function Filter MeasureTheory Topology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma isGDelta_probability_null_closed
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] {C : Set X} (hC : IsClosed C) :
    IsGδ {μ : ProbabilityMeasure X | (μ : Measure X) C = 0} := by
  have hsc : UpperSemicontinuous (fun μ : ProbabilityMeasure X => (μ : Measure X) C) :=
    upperSemicontinuous_iff_limsup_le.mpr (fun μ =>
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto tendsto_id hC)
  have heq : {μ : ProbabilityMeasure X | (μ : Measure X) C = 0} =
      ⋂ n : ℕ, {μ : ProbabilityMeasure X |
        (μ : Measure X) C < ENNReal.ofReal (1 / (n + 1 : ℝ))} := by
    ext μ
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h n
      rw [h]
      exact ENNReal.ofReal_pos.mpr (by positivity)
    · intro h
      apply le_antisymm _ zero_le
      have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
        simpa only [ENNReal.ofReal_zero, Function.comp_def] using
          ENNReal.continuous_ofReal.continuousAt.tendsto.comp
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact ge_of_tendsto' ht (fun n => (h n).le)
  rw [heq]
  exact IsGδ.iInter_of_isOpen (fun n => hsc.isOpen_preimage _)

lemma isGDelta_supported_probabilities
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] {S : Set X} (hS : IsGδ S) :
    IsGδ {μ : ProbabilityMeasure X | (μ : Measure X) Sᶜ = 0} := by
  obtain ⟨U, hU, rfl⟩ := hS.eq_iInter_nat
  have heq : {μ : ProbabilityMeasure X | (μ : Measure X) (⋂ n, U n)ᶜ = 0} =
      ⋂ n, {μ : ProbabilityMeasure X | (μ : Measure X) (U n)ᶜ = 0} := by
    ext μ
    simp only [mem_ofPred_eq, mem_iInter, compl_iInter, measure_iUnion_null_iff]
  rw [heq]
  exact IsGδ.iInter (fun n => isGDelta_probability_null_closed (hU n).isClosed_compl)

end CircleDomainRigidity

end

end OAI
