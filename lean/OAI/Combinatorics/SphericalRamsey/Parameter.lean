import OAI.Combinatorics.SphericalRamsey.Specification
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.Localization.Integral

namespace OAI

noncomputable section

namespace GrahamSpherical

/-- The native series includes the additional factorial-zero term. -/
theorem parameter_add_tenth :
    (1 : ℝ) / 10 + parameter = liouvilleNumber 10 := by
  simpa [LiouvilleNumber.partialSum, LiouvilleNumber.remainder, parameter] using
    (LiouvilleNumber.partialSum_add_remainder (m := (10 : ℝ)) (by norm_num) 0)

theorem parameter_eq_liouville_sub :
    parameter = liouvilleNumber 10 - (1 : ℝ) / 10 := by
  linarith [parameter_add_tenth]

/-- Transcendence of the factorial-series parameter, over the rational field. -/
theorem parameter_transcendental : Transcendental ℚ parameter := by
  intro hp
  have hrat : IsAlgebraic ℚ ((1 : ℝ) / 10) := by
    simpa using (isAlgebraic_ratCast ℚ (1 / 10 : ℚ) :
      IsAlgebraic ℚ ((1 / 10 : ℚ) : ℝ))
  have hsum : IsAlgebraic ℚ (liouvilleNumber 10) := by
    rw [← parameter_add_tenth]
    exact hrat.add hp
  have hint : IsAlgebraic ℤ (liouvilleNumber 10) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hsum
  exact (transcendental_liouvilleNumber (m := 10) (by norm_num)) hint

/-- The strict rational bounds stated for the literal factorial series. -/
theorem parameter_bounds :
    (11 : ℝ) / 100 < parameter ∧ parameter < 12 / 100 := by
  have hsplit := LiouvilleNumber.partialSum_add_remainder
    (m := (10 : ℝ)) (by norm_num) 2
  have hpos := LiouvilleNumber.remainder_pos (m := (10 : ℝ)) (by norm_num) 2
  have hupp := LiouvilleNumber.remainder_lt (m := (10 : ℝ)) 2 (by norm_num)
  norm_num [LiouvilleNumber.partialSum, Finset.sum_range_succ, Nat.factorial] at hsplit hupp
  constructor <;> linarith [parameter_add_tenth]

end GrahamSpherical

end

end OAI
