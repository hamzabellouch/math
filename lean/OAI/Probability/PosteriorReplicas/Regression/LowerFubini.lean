import OAI.Probability.PosteriorReplicas.Regression.Fubini

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
section LowerFubini
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
lemma prod_null_set_lower_bound {S : Set (X × Y)} (hS : NullMeasurableSet S (μ.prod ν))
    {c : ℝ≥0∞} (h : ∀ᵐ x ∂μ, c ≤ ν {y | (x,y) ∈ S}) :
    c * μ univ ≤ (μ.prod ν) S := by
  have hm : AEMeasurable (S.indicator (fun _ => (1 : ℝ≥0∞))) (μ.prod ν) :=
    aemeasurable_const.indicator₀ hS
  rw [← one_mul ((μ.prod ν) S), ← lintegral_indicator_const₀ hS 1, lintegral_prod _ hm]
  have hc : c * μ univ = ∫⁻ _ : X, c ∂μ := (lintegral_const c).symm
  rw [hc]
  apply lintegral_mono_ae
  filter_upwards [h, ae_fiber_aemeasurable hm.prod_swap] with x hx hmx
  have hs : NullMeasurableSet {y | (x,y) ∈ S} ν := by
    have heq : {y | (x,y) ∈ S} = {y | S.indicator (fun _ => (1 : ℝ≥0∞)) (x,y) = 1} := by
      ext y
      by_cases hy : (x,y) ∈ S <;> simp [hy]
    rw [heq]
    exact nullMeasurableSet_eq_fun hmx aemeasurable_const
  change c ≤ ∫⁻ y, ({y | (x,y) ∈ S}).indicator (fun _ => (1 : ℝ≥0∞)) y ∂ν
  simpa [lintegral_indicator_const₀ hs] using hx
end LowerFubini

end PosteriorRegression
end

end OAI
