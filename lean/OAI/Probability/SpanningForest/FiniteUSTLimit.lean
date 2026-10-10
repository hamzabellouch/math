import OAI.Probability.SpanningForest.CylinderLimitMeasure
import OAI.Probability.SpanningForest.BinaryWeakConvergence
import OAI.Probability.SpanningForest.FiniteUSTMeasure
import OAI.Probability.SpanningForest.FUSFLawUnique

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem336

def finiteUSTProbabilityMeasure (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) : ProbabilityMeasure EdgeConfiguration :=
  ⟨finiteUSTMeasure K, finiteUSTMeasure_isProbabilityMeasure K hK⟩

theorem exists_finiteUST_limit
    (H : ℕ → FiniteSubgraphCode)
    (hH : ∀ n, (spanningTrees (H n)).Nonempty)
    (L : Finset EdgeCode → Finset EdgeCode → ℝ≥0∞)
    (hL : ∀ A B, Tendsto (fun n => ustCylinder (H n) A B) atTop (𝓝 (L A B))) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      (∀ A B, (μ : Measure EdgeConfiguration) (edgeCylinder A B) = L A B) ∧
      Tendsto (fun n => finiteUSTProbabilityMeasure (H n) (hH n)) atTop (𝓝 μ) := by
  let μn := fun n => finiteUSTProbabilityMeasure (H n) (hH n)
  have hsep : ∀ μ ν : ProbabilityMeasure EdgeConfiguration,
      (∀ p : Finset EdgeCode × Finset EdgeCode,
        (μ : Measure EdgeConfiguration) (edgeCylinder p.1 p.2) =
          (ν : Measure EdgeConfiguration) (edgeCylinder p.1 p.2)) → μ = ν := by
    intro μ ν h
    have : IsProbabilityMeasure (μ : Measure EdgeConfiguration) := μ.property
    apply ProbabilityMeasure.toMeasure_injective
    exact configurationMeasure_ext fun A B => h (A, B)
  obtain ⟨μ, hμ, hweak⟩ := exists_probabilityMeasure_tendsto_of_clopen_limits μn
    (fun p : Finset EdgeCode × Finset EdgeCode => edgeCylinder p.1 p.2)
    (fun p => isClopen_boolCylinder p.1 p.2) hsep
    (fun p => L p.1 p.2) (by
      intro p
      simpa only [μn, finiteUSTProbabilityMeasure, ProbabilityMeasure.coe_mk,
        finiteUSTMeasure_edgeCylinder] using hL p.1 p.2)
  exact ⟨μ, fun A B => hμ (A, B), hweak⟩

theorem exists_hasFUSFLaw_of_common_cylinder_limits
    (G : GraphCode) (H : ℕ → FiniteSubgraphCode)
    (hH : IsConnectedExhaustion G H)
    (hne : ∀ n, (spanningTrees (H n)).Nonempty)
    (L : Finset EdgeCode → Finset EdgeCode → ℝ≥0∞)
    (hL : ∀ H' : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H' →
      ∀ A B, Tendsto (fun n => ustCylinder (H' n) A B) atTop (𝓝 (L A B))) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G (μ : Measure EdgeConfiguration) id := by
  obtain ⟨μ, hμ, _⟩ := exists_finiteUST_limit H hne L (hL H hH)
  refine ⟨μ, (fun e => measurable_pi_apply e), ?_⟩
  intro H' hH' A B
  simpa only [← hμ A B, edgeCylinder, id_eq] using hL H' hH' A B

theorem finiteUSTMeasure_positiveCylinder (K : FiniteSubgraphCode)
    (A : Finset EdgeCode) :
    finiteUSTMeasure K {x | ∀ e ∈ A, x e = true} = ustCylinder K A ∅ := by
  simpa [edgeCylinder] using finiteUSTMeasure_edgeCylinder K A ∅

theorem exists_finiteUST_limit_of_inclusion_limits
    (H : ℕ → FiniteSubgraphCode)
    (hH : ∀ n, (spanningTrees (H n)).Nonempty)
    (L : Finset EdgeCode → ℝ≥0∞)
    (hL : ∀ A, Tendsto (fun n => ustCylinder (H n) A ∅) atTop (𝓝 (L A))) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      (∀ A, (μ : Measure EdgeConfiguration) {x | ∀ e ∈ A, x e = true} = L A) ∧
      Tendsto (fun n => finiteUSTProbabilityMeasure (H n) (hH n)) atTop (𝓝 μ) := by
  apply BinaryLaw.exists_weakLimit_of_positiveCylinder_limits
    (fun n => finiteUSTProbabilityMeasure (H n) (hH n)) L
  intro A
  simpa only [finiteUSTProbabilityMeasure, ProbabilityMeasure.coe_mk,
    finiteUSTMeasure_positiveCylinder] using hL A

theorem exists_hasFUSFLaw_of_common_inclusion_limits
    (G : GraphCode) (H : ℕ → FiniteSubgraphCode)
    (hH : IsConnectedExhaustion G H)
    (hne : ∀ H' : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H' →
      ∀ n, (spanningTrees (H' n)).Nonempty)
    (L : Finset EdgeCode → ℝ≥0∞)
    (hL : ∀ H' : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H' →
      ∀ A, Tendsto (fun n => ustCylinder (H' n) A ∅) atTop (𝓝 (L A))) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G (μ : Measure EdgeConfiguration) id := by
  obtain ⟨μ, hμ, _⟩ := exists_finiteUST_limit_of_inclusion_limits H (hne H hH) L (hL H hH)
  refine ⟨μ, (fun e => measurable_pi_apply e), ?_⟩
  intro H' hH' A B
  have hw : Tendsto (fun n => finiteUSTProbabilityMeasure (H' n) (hne H' hH' n))
      atTop (𝓝 μ) := by
    apply BinaryLaw.tendsto_iff_positiveCylinders.mpr
    intro C
    simpa only [finiteUSTProbabilityMeasure, ProbabilityMeasure.coe_mk,
      finiteUSTMeasure_positiveCylinder, hμ C] using hL H' hH' C
  have hc := BinaryLaw.tendsto_iff_signedCylinders.mp hw A B
  change Tendsto (fun n => finiteUSTMeasure (H' n) (edgeCylinder A B)) atTop
    (𝓝 ((μ : Measure EdgeConfiguration) (edgeCylinder A B))) at hc
  simp only [finiteUSTMeasure_edgeCylinder] at hc
  exact hc

end Problem336

end

end OAI
