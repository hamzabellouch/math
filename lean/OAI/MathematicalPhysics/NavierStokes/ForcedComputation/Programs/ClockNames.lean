import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LogarithmName
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.Reparametrization

namespace OAI

/-! Fast names for the internal logarithmic clock and the reciprocal clock
speed. These are operations on rational names, rather than real oracles. -/

namespace ForcedComputation
open ShearFlows

def shiftedTimeName (b : ℕ → RationalSpaceTime) : ℕ → ℚ := fun n => 1 + (b n).1

theorem shiftedTimeName_spec {y : SpaceTime} {b : ℕ → RationalSpaceTime}
    (hb : IsFastName b y) : IsFastRealName (shiftedTimeName b) (1 + y.1) := by
  intro n
  have h := (norm_fst_le (y - rationalPoint (b n))).trans (hb n)
  simpa only [shiftedTimeName, Rat.cast_add, Rat.cast_one, add_sub_add_left_eq_sub,
    Prod.fst_sub, rationalPoint, Real.norm_eq_abs] using h

def clockPointName {y : SpaceTime} (b : ℕ → RationalSpaceTime)
    (hy : 0 < 1 + y.1) (hb : IsFastName b y) : ℕ → RationalSpaceTime := fun n =>
  (logFastName (shiftedTimeName b) hy (shiftedTimeName_spec hb) n, (b n).2)

theorem clockPointName_spec {y : SpaceTime} (b : ℕ → RationalSpaceTime)
    (hy : 0 < 1 + y.1) (hb : IsFastName b y) :
    IsFastName (clockPointName b hy hb) (logClock y.1, y.2) := by
  intro n
  apply norm_prod_le_iff.mpr
  constructor
  · have h := logFastName_spec (shiftedTimeName b) hy (shiftedTimeName_spec hb) n
    change |Real.log (1 + y.1) -
      (logFastName (shiftedTimeName b) hy (shiftedTimeName_spec hb) n : ℝ)| ≤ errorTolerance n
    exact h
  · have h := (norm_snd_le (y - rationalPoint (b n))).trans (hb n)
    exact h

def reciprocalClockName (b : ℕ → RationalSpaceTime) : ℕ → ℚ := fun n =>
  (max (1 / 2) (1 + (b (n + 2)).1))⁻¹

theorem reciprocalClockName_spec {y : SpaceTime} (b : ℕ → RationalSpaceTime)
    (hy : (1 / 2 : ℝ) ≤ 1 + y.1) (hb : IsFastName b y) :
    IsFastRealName (reciprocalClockName b) ((1 + y.1)⁻¹) := by
  intro n
  have h : (QBall.mk (1 + (b (n + 2)).1) ((2 : ℚ) ^ (-((n + 2 : ℕ) : ℤ)))).Contains
      (1 + y.1) := by
    have h := shiftedTimeName_spec hb (n + 2)
    simpa only [QBall.Contains, shiftedTimeName, Rat.cast_zpow, Rat.cast_ofNat,
      zpow_neg, zpow_natCast, Rat.cast_inv, Rat.cast_pow, errorTolerance] using h
  have hy' : ((1 / 2 : ℚ) : ℝ) ≤ 1 + y.1 := by
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    exact hy
  have hInv := QBall.contains_invLower h (show (0 : ℚ) < 1 / 2 by norm_num) hy'
  change |(1 + y.1)⁻¹ - (reciprocalClockName b n : ℝ)| ≤ errorTolerance n
  have he : ((((2 : ℚ) ^ (-((n + 2 : ℕ) : ℤ))) / (1 / 2) ^ 2 : ℚ) : ℝ) =
      errorTolerance n := by
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat,
      zpow_neg, zpow_natCast, errorTolerance, pow_add, mul_inv_rev]
    norm_num
  simpa only [QBall.Contains, QBall.invLower, reciprocalClockName, he] using hInv

end ForcedComputation

end OAI
