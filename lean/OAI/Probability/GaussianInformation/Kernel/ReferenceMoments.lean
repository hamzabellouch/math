import Mathlib
import OAI.Probability.GaussianInformation.Kernel.ReferenceDensity

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ReferenceGaussian
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open GaussianTools

lemma mixture_upper {p d L : ℕ} (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (r : Fin L → ℝ) (hr : ∀ j,0 < r j) (X : Mat p d) (y : Fin p → ℝ) :
    mixture ν r X y ≤ (L:ℝ)⁻¹*∑ j,densityBound p (r j) := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ ∫ _u,densityBound p (r j) ∂ν := integral_mono (integrable_atDensity ν (hr j) X y)
      (integrable_const _) (fun u => atDensity_le (hr j) X y u)
    _ = _ := by simp

lemma integrable_log_mixture_rows {p d L : ℕ} (hL : 0 < L)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (r : Fin L → ℝ) (hr : ∀ j,0 < r j) (s : Vec d)
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ᵐ u ∂ν,u ∈ closedBall s R) (e : Fin p → ℝ) :
    Integrable (fun X : Mat p d => Real.log (mixture ν r X (applyRows X s+e)))
      (Measure.pi (fun _ : Fin p => scalarRow d)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  let j : Fin L := ⟨0,hL⟩
  let U : ℝ := (L:ℝ)⁻¹*∑ j,densityBound p (r j)
  have hU : 0 < U := by
    apply mul_pos (by positivity)
    exact Finset.sum_pos (fun j _ => densityBound_pos p (hr j)) ⟨j,Finset.mem_univ _⟩
  have hm : Measurable (fun X : Mat p d => Real.log (mixture ν r X (applyRows X s+e))) := by
    apply Measurable.log
    unfold mixture
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro l _
    have hi : Continuous (fun t : Mat p d × Vec d => atDensity (r l) t.1 (applyRows t.1 s+e) t.2) := by
      unfold atDensity labelDensity gaussianPDFReal applyRows
      fun_prop
    exact hi.stronglyMeasurable.integral_prod_right.measurable
  refine integrable_of_le_of_le hm.aestronglyMeasurable ?_ ?_
    ((integrable_const (-Real.log L)).add (integrable_log_shift_rows ν s hR hs (hr j) e))
    (integrable_const (Real.log U))
  · filter_upwards [] with X
    have h := local_log_lower hL ν ν (m := 1) (by norm_num) (by simp) r hr X
      (applyRows X s+e) s R hs j
    simpa using h
  · filter_upwards [] with X
    exact Real.log_le_log (mixture_pos hL ν r hr X _) (mixture_upper ν r hr X _)

lemma local_mixture_rows_ge {p d L : ℕ} (hL : 0 < L)
    (ν τ : Measure (Vec d)) [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    {m : ℝ} (hm : 0 < m) (hdom : ENNReal.ofReal m • τ ≤ ν)
    (r : Fin L → ℝ) (hr : ∀ j,0 < r j) (s : Vec d)
    {R R₀ : ℝ} (hR : 0 ≤ R) (hR₀ : 0 ≤ R₀)
    (hs : ∀ᵐ u ∂τ,u ∈ closedBall s R) (hs₀ : ∀ᵐ u ∂ν,u ∈ closedBall s R₀)
    (e : Fin p → ℝ) (j : Fin L) :
    Real.log m-Real.log L-(p:ℝ)*Real.log (r j)-(p:ℝ)/2*Real.log (2*Real.pi)-
      ((p:ℝ)*R^2+∑ i,e i^2)/(r j)^2 ≤
      (∫ X : Mat p d,Real.log (mixture ν r X (applyRows X s+e))
        ∂Measure.pi (fun _ : Fin p => scalarRow d)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have hi := integrable_log_shift_rows τ s hR hs (hr j) e
  have h := integral_mono ((integrable_const (Real.log m-Real.log L)).add hi)
    (integrable_log_mixture_rows hL ν r hr s hR₀ hs₀ e)
    (fun X => local_log_lower hL ν τ hm hdom r hr X (applyRows X s+e) s R hs j)
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) hi] at h
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at h
  have hb := log_shift_rows_local_ge τ s hR hs (hr j) e
  linarith

end ReferenceGaussian

end OAI
