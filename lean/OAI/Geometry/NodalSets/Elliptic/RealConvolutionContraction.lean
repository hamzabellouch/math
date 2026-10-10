import OAI.Geometry.NodalSets.Elliptic.RealCompactH1Approximation
import OAI.Geometry.NodalSets.Elliptic.RealCompactL2

namespace OAI

namespace Yau
open MeasureTheory Set ContinuousLinearMap
open scoped ContDiff Convolution
noncomputable section

theorem realL2Convolution_normed_norm_le {n : ℕ}
    (b : ContDiffBump (0 : Coord n)) (U : RealEuclideanL2 n) :
    ‖realL2Convolution (b.normed volume) U‖ ≤ ‖U‖ := by
  calc
    _ ≤ ∫ t, ‖b.normed volume t • realL2Translate (-t) U‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t, b.normed volume t * ‖U‖ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t ↦ by
        dsimp only
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (b.nonneg_normed t),
          realL2Translate_norm])
    _ = ‖U‖ := by rw [integral_mul_const, b.integral_normed, one_mul]

theorem real_normed_convolution_square_le {n : ℕ} (u : Coord n → ℝ)
    (hu : MemLp u 2 volume) (hc : HasCompactSupport u)
    (b : ContDiffBump (0 : Coord n)) :
    (∫ x, ((u ⋆ b.normed volume) x)^2) ≤ ∫ x, (u x)^2 := by
  have hv : ContDiff ℝ ∞ (u ⋆ b.normed volume) := (b.hasCompactSupport_normed (μ := volume)).contDiff_convolution_right
    (lsmul ℝ ℝ) (hu.locallyIntegrable (by norm_num)) b.contDiff_normed
  have hs : HasCompactSupport (u ⋆ b.normed volume) := hc.convolution (lsmul ℝ ℝ) (b.hasCompactSupport_normed (μ := volume))
  have hm := real_compact_continuous_memLp _ hv.continuous hs
  rw [← real_toLp_norm_sq _ hm, ← real_toLp_norm_sq u hu,
    ← realL2Convolution_eq_toLp u _ (real_compact_memLp_integrable u hu hc)
      hu b.contDiff_normed b.hasCompactSupport_normed hm]
  exact pow_le_pow_left₀ (norm_nonneg _) (realL2Convolution_normed_norm_le b _) 2

end
end Yau

end OAI
