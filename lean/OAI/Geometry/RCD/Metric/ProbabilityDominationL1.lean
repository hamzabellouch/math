import OAI.Geometry.RCD.Sobolev.WeakDensityDomination
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace OAI

/-! # Weak convergence with a common density bound tests every L1 function -/

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
theorem integral_difference_le_of_domination (μ ν : Measure X)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • μ)
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    dist (∫ x, f x ∂ν) (∫ x, g x ∂ν) ≤ C.toReal*(∫ x, |f x-g x| ∂μ) := by
  have hif := hf.of_measure_le_smul hC hν
  have hig := hg.of_measure_le_smul hC hν
  rw [Real.dist_eq,← integral_sub hif hig]
  apply abs_integral_le_integral_abs.trans
  have hi := integral_mono_measure hν (Eventually.of_forall fun x => abs_nonneg (f x-g x))
    (((hf.sub hg).abs).smul_measure hC)
  simpa only [integral_smul_measure,smul_eq_mul] using hi

theorem weak_probability_integral_L1 (μ : Measure X) [μ.WeaklyRegular]
    (P : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
    (hlim : Tendsto P atTop (𝓝 Q)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hP : ∀ k, (P k : Measure X) ≤ C • μ)
    {f : X → ℝ} (hf : Integrable f μ) :
    Tendsto (fun k => ∫ x, f x ∂(P k : Measure X)) atTop (𝓝 (∫ x, f x ∂(Q : Measure X))) := by
  have hQ := weak_probability_domination μ P Q hlim hC hP
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε/(4*(C.toReal+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨g,hg,hgi⟩ := hf.exists_boundedContinuous_integral_sub_le hδ
  have hconv := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim g
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hconv (ε/2) (half_pos hε)
  refine ⟨N,fun k hk => ?_⟩
  have h1 := integral_difference_le_of_domination μ (P k : Measure X) hC (hP k) hf hgi
  have h3 := integral_difference_le_of_domination μ (Q : Measure X) hC hQ hf hgi
  have hg' : (∫ x, |f x-g x| ∂μ) ≤ δ := by simpa only [Real.norm_eq_abs] using hg
  have hsmall : 2*C.toReal*δ < ε/2 := by
    have he : 4*(C.toReal+1)*δ = ε := mul_div_cancel₀ ε (by positivity)
    nlinarith [ENNReal.toReal_nonneg (a := C)]
  have htri := dist_triangle4 (∫ x, f x ∂(P k : Measure X)) (∫ x, g x ∂(P k : Measure X))
    (∫ x, g x ∂(Q : Measure X)) (∫ x, f x ∂(Q : Measure X))
  rw [dist_comm (∫ x, g x ∂(Q : Measure X))] at htri
  have h2 := hN k hk
  have hb := mul_le_mul_of_nonneg_left hg' (ENNReal.toReal_nonneg (a := C))
  linarith

theorem weak_probability_integral_L1_varying (μ : Measure X) [μ.WeaklyRegular]
    (P : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
    (hlim : Tendsto P atTop (𝓝 Q)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hP : ∀ k, (P k : Measure X) ≤ C • μ)
    (F : ℕ → X → ℝ) (f : X → ℝ) (hF : ∀ k, Integrable (F k) μ) (hf : Integrable f μ)
    (he : Tendsto (fun k => ∫ x, |F k x-f x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, F k x ∂(P k : Measure X)) atTop (𝓝 (∫ x, f x ∂(Q : Measure X))) := by
  have hfixed := weak_probability_integral_L1 μ P Q hlim hC hP hf
  have herr : Tendsto (fun k => (∫ x, F k x ∂(P k : Measure X))-
      (∫ x, f x ∂(P k : Measure X))) atTop (𝓝 0) := by
    apply squeeze_zero_norm
      (fun k => ?_) (by simpa only [mul_zero] using he.const_mul C.toReal)
    simpa only [Real.dist_eq,Real.norm_eq_abs] using
      integral_difference_le_of_domination μ (P k : Measure X) hC (hP k) (hF k) hf
  convert hfixed.add herr using 1 <;> simp

end RegularPointCoordinates

end

end OAI
