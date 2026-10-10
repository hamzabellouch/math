import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulombRadial
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarModeDecay

namespace OAI

/-! Exponential off-site density leakage for the actual localized modes. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem positionSplitCoordinates_fst_norm_le (x : Position) :
    ‖(positionSplitCoordinates x).1‖ ≤ ‖x‖ := by
  have h := positionSplitCoordinates_norm_sq x
  nlinarith [sq_nonneg (positionSplitCoordinates x).2, norm_nonneg x,
    norm_nonneg (positionSplitCoordinates x).1]

theorem continuumLocalizedMode_planar_tail {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) (hr : 1 ≤ ‖(positionSplitCoordinates x).1 - u‖) :
    continuumLocalizedMode freq u x ≤ 4 * localizedAmplitudeBound freq *
      Real.exp (-(‖(positionSplitCoordinates x).1 - u‖ - 1) / 2) := by
  have hp := div_le_div_of_nonneg_right (planarResolventMode_exponential_tail hr)
    (Real.sqrt_nonneg (∫ r, planarResolventMode r ^ 2))
  have hv : verticalMode freq (positionSplitCoordinates x).2 ≤
      1 / Real.sqrt (Real.sqrt (Real.pi / freq)) := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (positionSplitCoordinates x).2])
  change (planarResolventMode ((positionSplitCoordinates x).1 - u) /
    Real.sqrt (∫ r, planarResolventMode r ^ 2)) * verticalMode freq (positionSplitCoordinates x).2 ≤ _
  calc
    _ ≤ (4 * Real.exp (-(‖(positionSplitCoordinates x).1 - u‖ - 1) / 2) /
        Real.sqrt (∫ r, planarResolventMode r ^ 2)) *
          (1 / Real.sqrt (Real.sqrt (Real.pi / freq))) :=
      mul_le_mul hp hv (verticalMode_positive hfreq _).le (by positivity)
    _ = _ := by unfold localizedAmplitudeBound; ring

def localizedTailConstant (freq : ℝ) : ℝ :=
  (4 * localizedAmplitudeBound freq) ^ 2 * Real.exp 1

theorem localizedTailConstant_nonnegative (freq : ℝ) : 0 ≤ localizedTailConstant freq :=
  mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem localizedDensity_planar_tail {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) (hr : 1 ≤ ‖(positionSplitCoordinates x).1 - u‖) :
    localizedDensity freq u x ≤ localizedTailConstant freq *
      Real.exp (-‖(positionSplitCoordinates x).1 - u‖) := by
  have h := (sq_le_sq₀ (continuumLocalizedMode_positive hfreq u x).le
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (localizedAmplitudeBound_positive hfreq).le) (Real.exp_pos _).le)).mpr
    (continuumLocalizedMode_planar_tail hfreq u x hr)
  have he : Real.exp (-(‖(positionSplitCoordinates x).1 - u‖ - 1) / 2) ^ 2 =
      Real.exp 1 * Real.exp (-‖(positionSplitCoordinates x).1 - u‖) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, he] at h
  simpa only [localizedDensity, localizedTailConstant, mul_assoc] using h

theorem localizedDensity_near_other_center {freq R : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) (x : Position) (hx : ‖x - planarCenter v‖ ≤ R)
    (hsep : R + 1 ≤ ‖u - v‖) :
    localizedDensity freq u x ≤ localizedTailConstant freq * Real.exp (R - ‖u - v‖) := by
  have hp : ‖(positionSplitCoordinates x).1 - v‖ ≤ R := by
    have h := (positionSplitCoordinates_fst_norm_le (x - planarCenter v)).trans hx
    simpa only [map_sub, planarCenter, ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub] using h
  have ht : ‖u - v‖ ≤ ‖u - (positionSplitCoordinates x).1‖ +
      ‖(positionSplitCoordinates x).1 - v‖ := by
    simpa only [dist_eq_norm] using dist_triangle u (positionSplitCoordinates x).1 v
  rw [norm_sub_rev u (positionSplitCoordinates x).1] at ht
  have hr : 1 ≤ ‖(positionSplitCoordinates x).1 - u‖ := by linarith
  exact (localizedDensity_planar_tail hfreq u x hr).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (localizedTailConstant_nonnegative freq))

end ContinuumCoulomb

end

end OAI
