import Mathlib
import OAI.Geometry.SmoothYau.SphereMetric.ComplexRealResponse

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
universe uFinWaves
namespace YauCounterexamples

lemma finite_gaussian_superposition_smallBall {I : Type uFinWaves} [Fintype I]
    (J : I → Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ) (b : (Fin 1 ⊕ Fin 3) → ℝ)
    (i₀ : I) (r : ℝ) (q : ℝ≥0∞)
    (hsmall : ∀ (Ω : Type uFinWaves) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (J i₀) v.2+noise v.1 ∈ Metric.closedBall 0 r} ≤ q) :
    (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
      {γ | (∑ i, complexRealResponse (J i) (γ i))+b ∈ Metric.closedBall 0 r} ≤ q := by
  classical
  let O := {i : I // i ≠ i₀}
  let S := {i : I // ¬i ≠ i₀}
  let ν := Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)
  let μ := Measure.pi (fun _ : O => ν)
  let f := fun γ : I → Fin 3 → ℂ => ((fun i : O => γ i), γ i₀)
  have hf : MeasurePreserving f (Measure.pi (fun _ : I => ν)) (μ.prod ν) := by
    have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : I => ν) (fun i => i ≠ i₀)
    have he := measurePreserving_eval (fun _ : S => ν) (⟨i₀,by simp⟩ : S)
    exact ((MeasurePreserving.id μ).prod he).comp hp
  let noise : (O → Fin 3 → ℂ) → ((Fin 1 ⊕ Fin 3) → ℝ) :=
    fun γ => (∑ i : O, complexRealResponse (J i) (γ i))+b
  have hn : Measurable noise := by
    dsimp only [noise]
    exact (Finset.measurable_sum _ (fun i _ =>
      (measurable_complexRealResponse _).comp (measurable_pi_apply i))).add measurable_const
  have hm : MeasurableSet {v : (O → Fin 3 → ℂ) × (Fin 3 → ℂ) |
      complexRealResponse (J i₀) v.2+noise v.1 ∈ Metric.closedBall 0 r} :=
    ((measurable_complexRealResponse _).comp measurable_snd |>.add
      (hn.comp measurable_fst)) Metric.isClosed_closedBall.measurableSet
  have hsum (γ : I → Fin 3 → ℂ) :
      (∑ i : O, complexRealResponse (J i) (γ i))+complexRealResponse (J i₀) (γ i₀) =
      ∑ i, complexRealResponse (J i) (γ i) := by
    have hs : (∑ i : S, complexRealResponse (J i) (γ i)) =
        complexRealResponse (J i₀) (γ i₀) := by
      apply (Fintype.sum_eq_single (⟨i₀,by simp⟩ : S) ?_).trans rfl
      intro i hi
      exact (hi (Subtype.ext (Classical.not_not.mp i.2))).elim
    simpa only [←hs] using Fintype.sum_subtype_add_sum_subtype (fun i => i ≠ i₀)
      (fun i => complexRealResponse (J i) (γ i))
  have heq : f ⁻¹' {v | complexRealResponse (J i₀) v.2+noise v.1 ∈ Metric.closedBall 0 r} =
      {γ | (∑ i, complexRealResponse (J i) (γ i))+b ∈ Metric.closedBall 0 r} := by
    ext γ
    change complexRealResponse (J i₀) (γ i₀)+
      ((∑ i : O, complexRealResponse (J i) (γ i))+b) ∈ Metric.closedBall 0 r ↔ _
    rw [←add_assoc,add_comm (complexRealResponse (J i₀) (γ i₀)),hsum]
    rfl
  rw [←heq,hf.measure_preimage hm.nullMeasurableSet]
  exact hsmall _ μ noise hn

end YauCounterexamples
end

end OAI
