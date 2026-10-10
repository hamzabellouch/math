import OAI.Dynamics.StandardMap.ContractingGraphPack

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma measure_image_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (s : Set E) (f : E → E)
    (D : E → E →L[ℝ] E) (c C : ℝ) (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hinj : InjOn f s)
    (hlo : ∀ x ∈ s, c ≤ |(D x).det|) (hhi : ∀ x ∈ s, |(D x).det| ≤ C) :
    ENNReal.ofReal c*μ s ≤ μ (f '' s) ∧ μ (f '' s) ≤ ENNReal.ofReal C*μ s := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image μ hs hD hinj]
  constructor
  · calc
      _ = ∫⁻ x in s, ENNReal.ofReal c ∂μ := by simp
      _ ≤ _ := setLIntegral_mono' hs (fun x hx => ENNReal.ofReal_le_ofReal (hlo x hx))
  · calc
      _ ≤ ∫⁻ x in s, ENNReal.ofReal C ∂μ :=
        setLIntegral_mono' hs (fun x hx => ENNReal.ofReal_le_ofReal (hhi x hx))
      _ = _ := by simp

lemma weighted_image_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (s : Set E) (f : E → E)
    (D : E → E →L[ℝ] E) (c C : ℝ) (g : E → ℝ≥0∞) (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hinj : InjOn f s)
    (hlo : ∀ x ∈ s, c ≤ |(D x).det|) (hhi : ∀ x ∈ s, |(D x).det| ≤ C) :
    ENNReal.ofReal c*(∫⁻ x in s, g (f x) ∂μ) ≤ ∫⁻ x in f '' s, g x ∂μ ∧
      (∫⁻ x in f '' s, g x ∂μ) ≤ ENNReal.ofReal C*(∫⁻ x in s, g (f x) ∂μ) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hD hinj g]
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' hs (fun x hx => mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hlo x hx)) (by positivity))
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' hs (fun x hx => mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hhi x hx)) (by positivity))

lemma weighted_sweep_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (s : Set E) (f : E → E)
    (D : E → E →L[ℝ] E) (c : ℝ) (g w : E → ℝ≥0∞) (δ : ℝ≥0∞)
    (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hinj : InjOn f s)
    (hlo : ∀ x ∈ s, c ≤ |(D x).det|)
    (hobs : ∀ x ∈ s, w x ≤ g (f x)+δ) :
    ENNReal.ofReal c*(∫⁻ x in s, w x ∂μ) ≤
      (∫⁻ x in f '' s, g x ∂μ)+ENNReal.ofReal c*δ*μ s := by
  calc
    _ ≤ ENNReal.ofReal c*(∫⁻ x in s, g (f x)+δ ∂μ) :=
      mul_le_mul_of_nonneg_left (setLIntegral_mono' hs hobs) (by positivity)
    _ = ENNReal.ofReal c*(∫⁻ x in s, g (f x) ∂μ)+ENNReal.ofReal c*δ*μ s := by
      rw [lintegral_add_right _ measurable_const]
      simp [mul_add,mul_assoc]
    _ ≤ _ := add_le_add (by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hD hinj g,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_mono' hs (fun x hx => mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hlo x hx)) (by positivity))) le_rfl
end StandardMapEntropy

end OAI
