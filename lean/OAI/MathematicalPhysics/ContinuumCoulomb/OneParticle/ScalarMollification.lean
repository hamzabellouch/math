import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Support

namespace OAI

/-! Compact smooth approximation on the real line, including its derivative.
Only the one-dimensional approximation needed by the oscillator is built. -/

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff
namespace ContinuumCoulomb

def scalarMollifier (k : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1/((k:ℝ)+1)
  rOut := 2/((k:ℝ)+1)
  rIn_pos := one_div_pos.mpr (by positivity)
  rIn_lt_rOut := div_lt_div_of_pos_right (by norm_num) (by positivity)

theorem scalarMollifier_tendsto :
    Tendsto (fun k => (scalarMollifier k).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [scalarMollifier,mul_one_div,mul_zero] using h

def scalarMollification (f : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  (scalarMollifier k).normed volume ⋆ f

theorem scalarMollification_smooth {f : ℝ → ℝ} (hf : Continuous f) (k : ℕ) :
    ContDiff ℝ ∞ (scalarMollification f k) :=
  (scalarMollifier k).hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) (scalarMollifier k).contDiff_normed hf.locallyIntegrable

theorem scalarMollification_compact {f : ℝ → ℝ} (hf : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (scalarMollification f k) :=
  (scalarMollifier k).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hf

theorem scalarMollification_tendsto {f : ℝ → ℝ} (hf : Continuous f) (z : ℝ) :
    Tendsto (fun k => scalarMollification f k z) atTop (𝓝 (f z)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous scalarMollifier_tendsto hf z

theorem scalarMollification_deriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (k : ℕ) :
    deriv (scalarMollification f k) = scalarMollification (deriv f) k := by
  funext z
  have hs : ContDiff ℝ ∞ ((scalarMollifier k).normed volume) :=
    (scalarMollifier k).contDiff_normed
  exact (hc.hasDerivAt_convolution_right (lsmul ℝ ℝ)
    hs.continuous.locallyIntegrable hf z).deriv

theorem scalarMollification_bound {f : ℝ → ℝ} {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (k : ℕ) (z : ℝ) :
    ‖scalarMollification f k z‖ ≤ C := by
  have hs : ContDiff ℝ ∞ ((scalarMollifier k).normed volume) :=
    (scalarMollifier k).contDiff_normed
  have hi : Integrable ((scalarMollifier k).normed volume) :=
    hs.continuous.integrable_of_hasCompactSupport (scalarMollifier k).hasCompactSupport_normed
  have h := norm_integral_le_of_norm_le (hi.mul_const C)
    (Filter.Eventually.of_forall fun y => show
      ‖(scalarMollifier k).normed volume y * f (z-y)‖ ≤
        (scalarMollifier k).normed volume y*C by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg ((scalarMollifier k).nonneg_normed y)]
      exact mul_le_mul_of_nonneg_left (hC (z-y)) ((scalarMollifier k).nonneg_normed y))
  simpa only [scalarMollification,convolution,lsmul_apply,smul_eq_mul,
    integral_mul_const,(scalarMollifier k).integral_normed,one_mul] using h

end ContinuumCoulomb

end

end OAI
