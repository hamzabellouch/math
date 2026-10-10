import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

namespace OAI

/-! Normalized smoothing preserves the precise scalar Lipschitz constant. -/
noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped NNReal Convolution ContDiff
namespace InvariantIsing

def gaussianSmooth {d : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] f

lemma gaussianSmooth_lipschitz {d : ℕ} {L : ℝ≥0}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f) :
    LipschitzWith L (gaussianSmooth φ f) := by
  have hi (x : EuclideanSpace ℝ (Fin d)) :
      Integrable (fun a => φ.normed volume a * f (x-a)) := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul] using
      (φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
        φ.continuous_normed hf.continuous.locallyIntegrable x)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖(∫ a, φ.normed volume a * f (x-a)) -
    (∫ a, φ.normed volume a * f (y-a))‖ ≤ (L : ℝ)*dist x y
  rw [← integral_sub (hi x) (hi y)]
  calc
    _ ≤ ∫ a, φ.normed volume a * ((L : ℝ)*dist x y) := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      filter_upwards [] with a
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (φ.nonneg_normed a)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed a)
      simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using
        hf.dist_le_mul (x-a) (y-a)
    _ = _ := by rw [integral_mul_const, φ.integral_normed, one_mul]

lemma gaussianSmooth_test {d : ℕ} {L : ℝ≥0}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f)
    (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (gaussianSmooth φ f) ∧ HasCompactSupport (gaussianSmooth φ f) := by
  exact ⟨φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed hf.continuous.locallyIntegrable,
    φ.hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hc⟩

lemma gaussianSmooth_dist_le {d : ℕ} {L : ℝ≥0}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f)
    (x : EuclideanSpace ℝ (Fin d)) :
    dist (gaussianSmooth φ f x) (f x) ≤ (L : ℝ)*φ.rOut := by
  apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans
    (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le L.coe_nonneg)

end InvariantIsing

end

end OAI
