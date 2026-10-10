import OAI.Combinatorics.EditApproximation.Geometry.Parameters
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A computable fixed-accuracy cutoff. The algorithm tests the small-log
conditions directly; it does not construct the double exponential bound. -/

namespace EditApproximation





def accuracyCutoffExponent (epsilon : ℚ) : ℕ := max (2 ^ 1000) ⌈10 / epsilon⌉₊

def accuracyCutoff (epsilon : ℚ) : ℕ := 2 ^ (2 ^ accuracyCutoffExponent epsilon)

theorem largeAccuracyInput_pos (N : ℕ) (epsilon : ℚ) (h : largeAccuracyInput N epsilon) : 0 < N := by
  have htwo : 2 ≤ (2 : ℕ) ^ 1000 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 1 ≤ 1000)
  have hell : 2 ≤ inputSmallLog N := htwo.trans h.1
  by_contra hn
  have hzero : N = 0 := Nat.eq_zero_of_not_pos hn
  rw [hzero] at hell
  norm_num [inputSmallLog, smallLogExponent, heightExponent] at hell

theorem heightExponent_above_double_power (N exponent : ℕ) (h : 2 ^ (2 ^ exponent) ≤ N) :
    exponent ≤ heightExponent N := by
  have hfirst := Nat.clog_mono_right 2 (h.trans (Nat.le_add_right N 2))
  rw [Nat.clog_pow _ _ (by decide : 1 < (2 : ℕ))] at hfirst
  have hsecond := Nat.clog_mono_right 2 hfirst
  simpa only [Nat.clog_pow _ _ (by decide : 1 < (2 : ℕ)), heightExponent] using hsecond

theorem accuracyCutoff_sufficient (N : ℕ) (epsilon : ℚ) (hepsilon : 0 < epsilon)
    (hN : accuracyCutoff epsilon ≤ N) : largeAccuracyInput N epsilon := by
  have hpositive : 0 < N := (Nat.two_pow_pos _).trans_le hN
  have he : accuracyCutoffExponent epsilon ≤ inputSmallLog N :=
    (heightExponent_above_double_power N (accuracyCutoffExponent epsilon) hN).trans
      (inputSmallLog_bounds N hpositive).1
  constructor
  · exact (le_max_left _ _).trans he
  · have hc : (10 / epsilon : ℚ) ≤ (inputSmallLog N : ℚ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans he))
    exact (div_le_iff₀ hepsilon).mp hc

theorem largeAccuracyInput_real (N : ℕ) (epsilon : ℚ) (h : largeAccuracyInput N epsilon) :
    2 ^ 1000 ≤ inputSmallLog N ∧ 10 ≤ (inputSmallLog N : ℝ) * (epsilon : ℝ) :=
  ⟨h.1, by exact_mod_cast h.2⟩

end EditApproximation

end OAI
