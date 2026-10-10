import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalRieszFinite
import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalRieszDecay

namespace OAI

/-! # Uniform integrated errors at the nearby points used for unsmoothing -/

namespace Ostmann

open Complex

theorem sqrt_log_nearby_lower (X Y : ℝ) (hX : 4 ≤ X) (hY : X / 2 ≤ Y) :
    Real.sqrt (Real.log X) / 2 ≤ Real.sqrt (Real.log Y) := by
  have hXp : 0 < X := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hYp : 0 < Y := by linarith
  have hsq : X ≤ Y ^ 2 := by nlinarith
  have hl := Real.log_le_log hXp hsq
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  nlinarith [Real.sq_sqrt (Real.log_nonneg (show 1 ≤ X by linarith)),
    Real.sq_sqrt (Real.log_nonneg hY1), Real.sqrt_nonneg (Real.log X),
    Real.sqrt_nonneg (Real.log Y)]

theorem principalRiesz_nearby_error (N : ℕ) (d X Y : ℝ) (hd : 0 < d)
    (hX : 4 ≤ X) (hY : X / 2 ≤ Y) (hY2 : Y ≤ 2 * X) (hYN : Y ≤ N)
    (herr : ‖principalRieszMean Y - (Y / 2 : ℝ)‖ ≤
      3 * Y * Real.exp (-d * Real.sqrt (Real.log Y))) :
    |finiteRieszSum (Finset.range (N + 1)) ArithmeticFunction.vonMangoldt Y - Y ^ 2 / 2| ≤
      12 * X ^ 2 * Real.exp (-(d / 2) * Real.sqrt (Real.log X)) := by
  have hYp : 0 < Y := by linarith
  have hroot := sqrt_log_nearby_lower X Y hX hY
  have hexp : Real.exp (-d * Real.sqrt (Real.log Y)) ≤
      Real.exp (-(d / 2) * Real.sqrt (Real.log X)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [principalRieszMean_finite_error N Y hYp hYN]
  calc
    _ ≤ Y * (3 * Y * Real.exp (-d * Real.sqrt (Real.log Y))) :=
      mul_le_mul_of_nonneg_left herr hYp.le
    _ = 3 * Y ^ 2 * Real.exp (-d * Real.sqrt (Real.log Y)) := by ring
    _ ≤ 12 * X ^ 2 * Real.exp (-(d / 2) * Real.sqrt (Real.log X)) := by
      apply mul_le_mul _ hexp (Real.exp_nonneg _) (by positivity)
      nlinarith

end Ostmann

end OAI
