import OAI.Analysis.Unitarizability.FiniteSynthesis
import OAI.Analysis.Unitarizability.SignMatrix

namespace OAI

/-! Complexification preserves real synthesis norm bounds.
The real and imaginary coefficient vectors are handled separately. -/
noncomputable section
namespace Dixmier
namespace ComplexFrames
open Finset
variable {I K : Type*} [Fintype K]
local instance : DecidableEq I := Classical.decEq I

def ofReal (v : EuclideanSpace ℝ K) : EuclideanSpace ℂ K := WithLp.toLp 2 (fun a => (v a : ℂ))
def realPart (z : EuclideanSpace ℂ K) : EuclideanSpace ℝ K := WithLp.toLp 2 (fun a => (z a).re)
def imagPart (z : EuclideanSpace ℂ K) : EuclideanSpace ℝ K := WithLp.toLp 2 (fun a => (z a).im)

theorem ofReal_norm (v : EuclideanSpace ℝ K) : ‖ofReal v‖ = ‖v‖ := by
  have h : ‖ofReal v‖^2 = ‖v‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, ofReal, Complex.norm_real]
  nlinarith [norm_nonneg (ofReal v), norm_nonneg v]

theorem norm_sq_split (z : EuclideanSpace ℂ K) :
    ‖z‖^2 = ‖realPart z‖^2 + ‖imagPart z‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, realPart, imagPart,
    Real.norm_eq_abs, sq_abs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem synthesis_realPart (v : I → EuclideanSpace ℝ K) (J : Finset I) (z : EuclideanSpace ℂ J) :
    realPart (FiniteSynthesis.synthesis (fun i => ofReal (v i)) J z) =
      ∑ i : J, (realPart z) i • v i := by
  ext a
  simp only [FiniteSynthesis.synthesis_apply, realPart, ofReal, WithLp.ofLp_toLp,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem synthesis_imagPart (v : I → EuclideanSpace ℝ K) (J : Finset I) (z : EuclideanSpace ℂ J) :
    imagPart (FiniteSynthesis.synthesis (fun i => ofReal (v i)) J z) =
      ∑ i : J, (imagPart z) i • v i := by
  ext a
  simp only [FiniteSynthesis.synthesis_apply, imagPart, ofReal, WithLp.ofLp_toLp,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Complex.im_sum,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]

theorem synthesis_bound (v : I → EuclideanSpace ℝ K) (J : Finset I) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ z : EuclideanSpace ℝ J, ‖∑ i : J, z i • v i‖ ≤ b*‖z‖) :
    ‖FiniteSynthesis.synthesis (fun i => ofReal (v i)) J‖ ≤ b := by
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro z
  have hr := pow_le_pow_left₀ (norm_nonneg _) (h (realPart z)) 2
  have hi := pow_le_pow_left₀ (norm_nonneg _) (h (imagPart z)) 2
  have hsq : ‖FiniteSynthesis.synthesis (fun i => ofReal (v i)) J z‖^2 ≤ b^2*‖z‖^2 := by
    rw [norm_sq_split, synthesis_realPart, synthesis_imagPart, norm_sq_split z]
    nlinarith [hr, hi]
  nlinarith [norm_nonneg (FiniteSynthesis.synthesis (fun i => ofReal (v i)) J z),
    norm_nonneg z, mul_nonneg hb (norm_nonneg z)]

end ComplexFrames
end Dixmier

end

end OAI
