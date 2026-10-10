import OAI.NumberTheory.CubicMoment.Estimates.PrimaryPrimePNTProofAP
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryPrimePNTProofCounting
import OAI.NumberTheory.CubicMoment.Estimates.ModelPartialSummation

namespace OAI

/-! The primary-prime PNT, from rational progressions and actual Eisenstein splitting. -/
noncomputable section
open Filter Topology Asymptotics
namespace CubicFirstMoment

private lemma sqrt_log_remainder_tendsto_zero :
    Tendsto (fun X : ℝ => 2 * (Real.sqrt X + 1) * Real.log X / X)
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun X : ℝ => Real.log X / X) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_atTop zero_lt_one).tendsto_div_nhds_zero
  have h := sqrt_log_div_tendsto_zero.add (h1.const_mul 2)
  norm_num only [add_zero, mul_zero] at h
  convert h using 1
  ext X
  ring

/-- The ordinary prime-ideal theorem in exactly the normalization used by the mains.
No prime-distribution or splitting hypothesis remains. -/
theorem primaryPrimePNT_proved : PrimaryPrimePNT := by
  classical
  have hcount (X : ℝ) :
      ((Nat.primesLE ⌊X⌋₊).filter (fun p => p % 3 = 1)).card =
        (rationalProgressionPrimes 1 X).card := by
    apply congrArg Finset.card
    ext p
    simp only [rationalProgressionPrimes, Finset.mem_filter]
  have hm : Tendsto (fun X => 2 * rationalProgressionCount 1 X * Real.log X / X)
      atTop (𝓝 1) := by
    have h := rationalProgressionCount_one_limit.const_mul 2
    norm_num at h
    convert h using 1
    ext X
    ring
  have hu := hm.add sqrt_log_remainder_tendsto_zero
  norm_num at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hm hu
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hcmp := (primaryPrimeCount_comparison X (by linarith)).1
    rw [hcount] at hcmp
    have hc : 2 * rationalProgressionCount 1 X ≤ primaryPrimeCount X := by
      unfold rationalProgressionCount primaryPrimeCount
      exact_mod_cast hcmp
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.log_nonneg hX)) (by linarith)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hcmp := (primaryPrimeCount_comparison X (by linarith)).2
    rw [hcount] at hcmp
    have hc : primaryPrimeCount X ≤ 2 * rationalProgressionCount 1 X +
        2 * (Nat.sqrt ⌊X⌋₊ + 1 : ℕ) := by
      unfold rationalProgressionCount primaryPrimeCount
      exact_mod_cast hcmp
    have hroot : (Nat.sqrt ⌊X⌋₊ : ℝ) ≤ Real.sqrt X := by
      have hs := Nat.sqrt_le' ⌊X⌋₊
      have hs' : (Nat.sqrt ⌊X⌋₊ : ℝ) ^ 2 ≤ X := by
        exact (by exact_mod_cast hs : (Nat.sqrt ⌊X⌋₊ : ℝ) ^ 2 ≤ ⌊X⌋₊).trans
          (Nat.floor_le (by linarith))
      nlinarith [Real.sqrt_nonneg X, Real.sq_sqrt (show 0 ≤ X by linarith),
        (show (0 : ℝ) ≤ (Nat.sqrt ⌊X⌋₊ : ℝ) by positivity)]
    have hc' : primaryPrimeCount X ≤
        2 * rationalProgressionCount 1 X + 2 * (Real.sqrt X + 1) := by
      push_cast at hc
      linarith
    have hb := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc' (Real.log_nonneg hX)) (show 0 ≤ X by linarith)
    simpa only [add_mul, add_div] using hb

end CubicFirstMoment

end

end OAI
