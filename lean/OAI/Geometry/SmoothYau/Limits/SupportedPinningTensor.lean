import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.BundleRankOne
import OAI.Geometry.SmoothYau.Spectrum.BilinearTransverse

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma supportedPinningTensor_eq (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M) :
    supportedPinningTensor g u v χ x =
      χ x • bilinearPinning (E := E) (g.inner x) (metricGradient g u x) (metricGradient g v x) := rfl

lemma supportedPinningTensor_selfAdjoint (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M)
    (a b : TangentSpace 𝓘(ℝ,E) x) :
    g.inner x (supportedPinningTensor g u v χ x a) b =
      g.inner x a (supportedPinningTensor g u v χ x b) := by
  rw [supportedPinningTensor_eq]
  change (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x)
      (χ x • bilinearPinning (E := E) (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x)
        (metricGradient g u x) (metricGradient g v x) (show E from a)) (show E from b) =
    (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x) (show E from a)
      (χ x • bilinearPinning (E := E) (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x)
        (metricGradient g u x) (metricGradient g v x) (show E from b))
  erw [map_smul, smul_apply, map_smul]
  change χ x * _ = χ x * _
  exact congrArg (fun r : ℝ => χ x * r)
    (bilinearPinning_selfAdjoint (E := E) (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x)
      (g.symm x) (metricGradient g u x) (metricGradient g v x) a b)

lemma supportedPinningTensor_kernel (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M)
    (hn : χ x ≠ 0 → metricGradient g u x ≠ 0) :
    supportedPinningTensor g u v χ x (metricGradient g u x) = 0 := by
  rw [supportedPinningTensor_eq]
  by_cases hχ : χ x = 0
  · simp only [hχ, zero_smul]
    rfl
  have ha := (g.pos x _ (hn hχ)).ne'
  change χ x • (bilinearPinning (E := E) _ _ _ _) = 0
  erw [bilinearPinning_kernel (E := E) _ (g.symm x) ha,smul_zero]

lemma supportedPinningTensor_trace (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M)
    (hn : χ x ≠ 0 → metricGradient g u x ≠ 0) (hd : Module.finrank ℝ E = 3) :
    LinearMap.trace ℝ (TangentSpace 𝓘(ℝ,E) x)
      (supportedPinningTensor g u v χ x).toLinearMap = 0 := by
  rw [supportedPinningTensor_eq]
  by_cases hχ : χ x = 0
  · simp only [hχ, zero_smul]
    change LinearMap.trace ℝ E (0 : E →ₗ[ℝ] E) = 0
    exact map_zero _
  have ha := (g.pos x _ (hn hχ)).ne'
  change LinearMap.trace ℝ _ (χ x • (bilinearPinning (E := E) _ _ _).toLinearMap) = 0
  erw [map_smul,bilinearPinning_trace (E := E) _ ha _ hd,smul_zero]

lemma supportedPinningTensor_quadratic (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M)
    (hn : χ x ≠ 0 → metricGradient g u x ≠ 0) :
    g.inner x (metricGradient g v x) (supportedPinningTensor g u v χ x (metricGradient g v x)) =
      χ x / 2 * (g.inner x (bundleTransverse g u x (metricGradient g v x))
        (bundleTransverse g u x (metricGradient g v x)))^2 := by
  rw [supportedPinningTensor_eq]
  by_cases hχ : χ x = 0
  · simp only [hχ, zero_smul, zero_div, zero_mul]
    change (g.inner x (metricGradient g v x)) 0 = 0
    exact map_zero _
  have ha := (g.pos x _ (hn hχ)).ne'
  change (show E →L[ℝ] ℝ from g.inner x (metricGradient g v x))
      (χ x • bilinearPinning (E := E) (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x)
        (metricGradient g u x) (metricGradient g v x) (show E from metricGradient g v x)) = _
  erw [map_smul, smul_eq_mul]
  have he := bilinearPinning_quadratic (E := E)
    (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x) (g.symm x) ha (metricGradient g v x)
  change g.inner x (metricGradient g v x)
    (bilinearPinning (E := E) (g.inner x) (metricGradient g u x) (metricGradient g v x)
      (metricGradient g v x)) = _ at he
  calc
    _ = χ x * ((g.inner x (bundleTransverse g u x (metricGradient g v x))
      (bundleTransverse g u x (metricGradient g v x)))^2 / 2) :=
        congrArg (fun r : ℝ => χ x * r) he
    _ = _ := by ring

lemma supportedPinningTensor_zero (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M)
    (hχ : χ x = 0) : supportedPinningTensor g u v χ x = 0 := by
  simp only [supportedPinningTensor_eq,hχ,zero_smul]
  rfl

lemma supportedPinningTensor_quadratic_pos (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M)
    (hχ : 0 < χ x) (hn : metricGradient g u x ≠ 0)
    (hp : bundleTransverse g u x (metricGradient g v x) ≠ 0) :
    0 < g.inner x (metricGradient g v x)
      (supportedPinningTensor g u v χ x (metricGradient g v x)) := by
  rw [supportedPinningTensor_quadratic g u v χ x (fun _ => hn)]
  exact mul_pos (div_pos hχ (by norm_num)) (sq_pos_of_pos (g.pos x _ hp))
end YauCounterexamples


end

end OAI
