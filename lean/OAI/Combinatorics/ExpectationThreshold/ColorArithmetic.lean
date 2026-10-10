import OAI.Combinatorics.ExpectationThreshold.ProbabilityColors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Exact normalization of the profile coefficient

At level `i+1`, the color probability is `256^(i+1)*p`. Its likelihood
factor cancels the density and turns the counting factor `3*4^(i+1)`
into the geometric coefficient `3/64^(i+1)`.
-/

namespace TalagrandThreshold

theorem profile_coefficient_eq {p : ℝ} (hp : 0 < p) (s : ℕ) (i : Fin s) :
    ((3 : ℝ) * (4 : ℝ) ^ (i.val + 1)) * (p / colorProb p s i.castSucc) =
      3 / (64 : ℝ) ^ (i.val + 1) := by
  rw [colorProb_castSucc]
  have hpne : p ≠ 0 := ne_of_gt hp
  have hpow : (256 : ℝ) ^ (i.val + 1) =
      (4 : ℝ) ^ (i.val + 1) * (64 : ℝ) ^ (i.val + 1) := by
    rw [← mul_pow]
    norm_num
  calc
    _ = 3 * ((4 : ℝ) ^ (i.val + 1) / (256 : ℝ) ^ (i.val + 1)) := by
      field_simp [hpne]
    _ = 3 / (64 : ℝ) ^ (i.val + 1) := by
      rw [hpow]
      field_simp

theorem profile_coefficient_pow_eq {p : ℝ} (hp : 0 < p)
    (s : ℕ) (i : Fin s) (t : ℕ) :
    ((3 : ℝ) * (4 : ℝ) ^ (i.val + 1)) ^ t *
        (p / colorProb p s i.castSucc) ^ t =
      (3 / (64 : ℝ) ^ (i.val + 1)) ^ t := by
  rw [← mul_pow, profile_coefficient_eq hp s i]

end TalagrandThreshold

end OAI
