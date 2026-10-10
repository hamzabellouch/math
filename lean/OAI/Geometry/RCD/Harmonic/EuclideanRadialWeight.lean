import OAI.Geometry.RCD.Harmonic.EuclideanHarmonicCompactExtension
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

/-! # A smooth radial averaging weight and its potential -/

open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

private theorem glue_derivative (t : ℝ) :
    deriv expNegInvGlue t = (t⁻¹)^2*expNegInvGlue t := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) t
  simpa using h.deriv

def euclideanRadialPotential (n : ℕ) (x : Euclidean n) : ℝ :=
  expNegInvGlue (1-‖x‖^2)

def euclideanRadialWeight (n : ℕ) (x : Euclidean n) : ℝ :=
  2*deriv expNegInvGlue (1-‖x‖^2)

theorem euclideanRadialPotential_smooth (n : ℕ) : ContDiff ℝ ∞ (euclideanRadialPotential n) :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

theorem euclideanRadialWeight_smooth (n : ℕ) : ContDiff ℝ ∞ (euclideanRadialWeight n) := by
  have hd : ContDiff ℝ ∞ (deriv expNegInvGlue) :=
    by
      apply ContDiff.deriv'
      simpa using (expNegInvGlue.contDiff (n := (⊤ : ℕ∞)))
  exact contDiff_const.mul (hd.comp (contDiff_const.sub (contDiff_norm_sq ℝ)))

theorem euclideanRadialWeight_nonneg (n : ℕ) (x : Euclidean n) :
    0 ≤ euclideanRadialWeight n x := by
  dsimp only [euclideanRadialWeight]
  rw [glue_derivative]
  exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg _))

theorem euclideanRadialWeight_zero_pos (n : ℕ) : 0 < euclideanRadialWeight n 0 := by
  simp only [euclideanRadialWeight,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),sub_zero,
    glue_derivative,inv_one,one_pow,one_mul]
  exact mul_pos (by norm_num) (expNegInvGlue.pos_of_pos zero_lt_one)

theorem euclideanRadialWeight_support (n : ℕ) :
    tsupport (euclideanRadialWeight n) ⊆ closedBall 0 1 := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hn
  have hx1 : 1 < ‖x‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hn
  apply hx
  dsimp only [euclideanRadialWeight]
  rw [glue_derivative,expNegInvGlue.zero_of_nonpos (by nlinarith),mul_zero,mul_zero]

theorem euclideanRadialPotential_support (n : ℕ) :
    tsupport (euclideanRadialPotential n) ⊆ closedBall 0 1 := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hn
  have hx1 : 1 < ‖x‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hn
  exact hx (expNegInvGlue.zero_of_nonpos (by nlinarith))

theorem euclideanRadialWeight_compact (n : ℕ) : HasCompactSupport (euclideanRadialWeight n) :=
  (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (euclideanRadialWeight_support n)

theorem euclideanRadialPotential_compact (n : ℕ) : HasCompactSupport (euclideanRadialPotential n) :=
  (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (euclideanRadialPotential_support n)

theorem euclideanRadialWeight_mass_pos (n : ℕ) :
    0 < ∫ x, euclideanRadialWeight n x :=
  (euclideanRadialWeight_smooth n).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (euclideanRadialWeight_compact n) (euclideanRadialWeight_nonneg n)
    (euclideanRadialWeight_zero_pos n).ne'

/-- The radial potential converts a dilation derivative into a gradient
pairing, to which the compact-test Green identity applies. -/
theorem euclideanRadialPotential_fderiv (n : ℕ) (x v : Euclidean n) :
    fderiv ℝ (euclideanRadialPotential n) x v =
      -euclideanRadialWeight n x*inner ℝ x v := by
  have hinner := (hasFDerivAt_const (1:ℝ) x).sub (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hd : HasDerivAt expNegInvGlue (deriv expNegInvGlue (1-‖x‖^2)) (1-‖x‖^2) :=
    ((expNegInvGlue.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp) _).hasDerivAt
  have hf := hd.comp_hasFDerivAt x hinner
  have he := congrArg (fun L : Euclidean n →L[ℝ] ℝ => L v) hf.fderiv
  change fderiv ℝ (euclideanRadialPotential n) x v = _ at he
  rw [he]
  simp only [smul_apply,sub_apply,zero_apply,smul_eq_mul,euclideanRadialWeight]
  simp only [innerSL_apply_apply]
  ring

end RegularPointCoordinates

end

end OAI
