import OAI.MeasureTheory.Falconer.Estimates.ComparableProfileFactor
import OAI.MeasureTheory.Falconer.Fourier.GoodSupportedKernelMajorant

namespace OAI

namespace PlanarFalconer
open scoped ENNReal

theorem comparable_normalized_bound (N : ℕ) (hN : 0 < N)
    (m : ℝ → ℝ) (a b v lam : ℝ) (c : ℕ) (H D : ℝ≥0∞) (F : ℂ)
    (hc : (c:ℝ) ≤ 4096*((2:ℝ)^N)^(2*(m b-m a)+12*lam))
    (hF : ‖F‖ₑ ≤ H * ENNReal.ofReal
      ((((2:ℝ)^N)^(-m b))^4*(2:ℝ)^(-2*(v-b))) * (c:ℝ≥0∞) * 257025537024256 * D) :
    ‖((2:ℝ)^(2*(v-a))/(((2:ℝ)^N)^(-m a))^4) • F‖ₑ ≤
      (H*257025537024256*4096) *
        ENNReal.ofReal (((2:ℝ)^N)^(-2*(m b-b/N-(m a-a/N))+12*lam)) * D := by
  let p : ℝ := (2:ℝ)^(2*(v-a))/(((2:ℝ)^N)^(-m a))^4
  let g : ℝ := (((2:ℝ)^N)^(-m b))^4*(2:ℝ)^(-2*(v-b))
  let r : ℝ := 4096*((2:ℝ)^N)^(2*(m b-m a)+12*lam)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hce : (c:ℝ≥0∞) ≤ ENNReal.ofReal r := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hc
  have hn : ‖p • F‖ₑ = ENNReal.ofReal p * ‖F‖ₑ := by
    simp only [← ofReal_norm,norm_smul,Real.norm_eq_abs,abs_of_nonneg hp,ENNReal.ofReal_mul hp]
  rw [hn]
  calc
    _ ≤ ENNReal.ofReal p * (H*ENNReal.ofReal g*(c:ℝ≥0∞)*257025537024256*D) :=
      mul_le_mul_right hF (ENNReal.ofReal p)
    _ ≤ ENNReal.ofReal p * (H*ENNReal.ofReal g*ENNReal.ofReal r*257025537024256*D) := by
      gcongr
    _ = H*257025537024256*ENNReal.ofReal (p*g*r)*D := by
      rw [ENNReal.ofReal_mul (mul_nonneg hp hg),ENNReal.ofReal_mul hp]
      ring
    _ = _ := by
      have he : p*g*r = 4096*((2:ℝ)^N)^(-2*(m b-b/N-(m a-a/N))+12*lam) :=
        comparable_profile_factor N hN m a b v lam
      rw [he,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4096)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring

end PlanarFalconer

end OAI
