import OAI.Probability.SLE.Multipoint.MultipointRegularizedField
import OAI.Probability.SLE.Multipoint.MultipointSwitches

namespace OAI

/-! Exact first-half and second-half formulas for the active multipoint
factor. The change of formula at the midpoint has no jump. -/

noncomputable section
open Set

namespace SLEExactGauge.Multipoint

/-- The source clock in logarithmic capacity-two coordinates. -/
def logFactorClock (κ : ℝ) (z : ℂ × ℝ) : ℝ := κ / 4 * (z.2-z.1.im)

def factorActivationScale (κ a : ℝ) : ℝ := Real.exp (-greenExponent κ*a/2)/3

lemma factorActivationScale_pos (κ a : ℝ) : 0 < factorActivationScale κ a :=
  div_pos (Real.exp_pos _) (by norm_num)

lemma first_branch_regulator (κ β a : ℝ) (z : ℂ × ℝ) :
    branchRegulator κ (Real.exp (β*a)) (-β) z =
      Real.exp (-β*(logFactorClock κ z-a)) := by
  unfold branchRegulator logFactorClock
  rw [← Real.exp_add]
  congr 1
  ring

lemma second_branch_regulator (κ β a U : ℝ) (z : ℂ × ℝ) :
    branchRegulator κ (Real.exp (-β*(U+a))) β z =
      Real.exp (-β*(U-(logFactorClock κ z-a))) := by
  unfold branchRegulator logFactorClock
  rw [← Real.exp_add]
  congr 1
  ring

lemma first_branch_regulator_eq (κ β a U : ℝ) (z : ℂ × ℝ)
    (hu : logFactorClock κ z-a ≤ U/2) :
    branchRegulator κ (Real.exp (β*a)) (-β) z =
      regulator β U (logFactorClock κ z-a) := by
  rw [first_branch_regulator, regulator_eq_left hu]

lemma second_branch_regulator_eq (κ β a U : ℝ) (z : ℂ × ℝ)
    (hu : U/2 ≤ logFactorClock κ z-a) :
    branchRegulator κ (Real.exp (-β*(U+a))) β z =
      regulator β U (logFactorClock κ z-a) := by
  rw [second_branch_regulator, regulator_eq_right hu]

lemma regularizedLogFactor_normalized (κ D σ a : ℝ) (z : ℂ × ℝ) (x : ℝ) :
    factorActivationScale κ a * regularizedLogFactor κ D σ z x =
      Real.exp (greenExponent κ/2*(logFactorClock κ z-a))/3 *
        angularFactor (greenExponent κ) (branchRegulator κ D σ z) (logAngle κ z x) := by
  rw [regularizedLogFactor_eq]
  unfold factorActivationScale
  have he : Real.exp (-greenExponent κ*a/2) *
      Real.exp (((greenExponent κ/2)*κ/4)*(z.2-z.1.im)) =
        Real.exp (greenExponent κ/2*(logFactorClock κ z-a)) := by
    rw [← Real.exp_add]
    congr 1
    unfold logFactorClock
    ring
  calc
    _ = (Real.exp (-greenExponent κ*a/2) *
        Real.exp (((greenExponent κ/2)*κ/4)*(z.2-z.1.im)))/3 *
        angularFactor (greenExponent κ) (branchRegulator κ D σ z) (logAngle κ z x) := by ring
    _ = _ := by rw [he]

lemma first_branch_factor_eq (κ β a U : ℝ) (z : ℂ × ℝ) (x : ℝ)
    (hu : logFactorClock κ z-a ≤ U/2) :
    factorActivationScale κ a *
      regularizedLogFactor κ (Real.exp (β*a)) (-β) z x =
        activeFactor (greenExponent κ) β U (logFactorClock κ z-a) (logAngle κ z x) := by
  rw [regularizedLogFactor_normalized, first_branch_regulator_eq κ β a U z hu]
  rfl

lemma second_branch_factor_eq (κ β a U : ℝ) (z : ℂ × ℝ) (x : ℝ)
    (hu : U/2 ≤ logFactorClock κ z-a) :
    factorActivationScale κ a *
      regularizedLogFactor κ (Real.exp (-β*(U+a))) β z x =
        activeFactor (greenExponent κ) β U (logFactorClock κ z-a) (logAngle κ z x) := by
  rw [regularizedLogFactor_normalized, second_branch_regulator_eq κ β a U z hu]
  rfl

lemma first_branch_regulator_le_one (κ β a : ℝ) (z : ℂ × ℝ)
    (hβ : 0 ≤ β) (hu : 0 ≤ logFactorClock κ z-a) :
    branchRegulator κ (Real.exp (β*a)) (-β) z ≤ 1 := by
  rw [first_branch_regulator]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) hu)

lemma second_branch_regulator_le_one (κ β a U : ℝ) (z : ℂ × ℝ)
    (hβ : 0 ≤ β) (hu : logFactorClock κ z-a ≤ U) :
    branchRegulator κ (Real.exp (-β*(U+a))) β z ≤ 1 := by
  rw [second_branch_regulator]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hβ) (sub_nonneg.mpr hu))

lemma first_branch_factor_pos (κ β a : ℝ) (z : ℂ × ℝ) (x : ℝ) :
    0 < factorActivationScale κ a *
      regularizedLogFactor κ (Real.exp (β*a)) (-β) z x :=
  mul_pos (factorActivationScale_pos κ a)
    (regularizedLogFactor_pos κ _ _ (Real.exp_pos _) z x)

lemma second_branch_factor_pos (κ β a U : ℝ) (z : ℂ × ℝ) (x : ℝ) :
    0 < factorActivationScale κ a *
      regularizedLogFactor κ (Real.exp (-β*(U+a))) β z x :=
  mul_pos (factorActivationScale_pos κ a)
    (regularizedLogFactor_pos κ _ _ (Real.exp_pos _) z x)

lemma branch_midpoint_eq (κ β a U : ℝ) (z : ℂ × ℝ) (x : ℝ)
    (hu : logFactorClock κ z-a = U/2) :
    regularizedLogFactor κ (Real.exp (β*a)) (-β) z x =
      regularizedLogFactor κ (Real.exp (-β*(U+a))) β z x := by
  rw [regularizedLogFactor_eq, regularizedLogFactor_eq,
    first_branch_regulator_eq κ β a U z hu.le,
    second_branch_regulator_eq κ β a U z hu.ge]

private lemma factorExponent_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < greenExponent κ := by
  unfold greenExponent
  rw [sub_pos, lt_div_iff₀ hκ]
  linarith

/-- Activation changes the inactive factor one downward to the first
smooth branch. -/
lemma first_branch_activation_le (κ β a U : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ × ℝ) (x : ℝ) (hU : 0 ≤ U) (hu : logFactorClock κ z-a = 0) :
    factorActivationScale κ a *
      regularizedLogFactor κ (Real.exp (β*a)) (-β) z x ≤ 1 := by
  rw [first_branch_factor_eq κ β a U z x (by rw [hu]; linarith), hu]
  exact activeFactor_activation_le (factorExponent_pos κ hκ hκ8) hU
    (logAngle_sin_pos κ z x).le

/-- Completion freezes at the angle-independent lower bound. -/
lemma second_branch_completion_jump (κ β a U : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ × ℝ) (x : ℝ) (hU : 0 ≤ U) (hu : logFactorClock κ z-a = U) :
    Real.exp (greenExponent κ/2*U)/3 ≤ factorActivationScale κ a *
      regularizedLogFactor κ (Real.exp (-β*(U+a))) β z x := by
  rw [second_branch_factor_eq κ β a U z x (by rw [hu]; linarith), hu]
  exact activeFactor_completion_jump (factorExponent_pos κ hκ hκ8) hU
    (logAngle_sin_pos κ z x).le

end SLEExactGauge.Multipoint

end

end OAI
