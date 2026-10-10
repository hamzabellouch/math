import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantMassEstimate

namespace OAI

/-! # A fixed smooth partition profile for the original logarithmic cells -/

namespace Ostmann
open Filter
open scoped Classical

noncomputable def logCellProfile (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1) - Real.smoothTransition x

noncomputable def logCellCentralLower : ℝ :=
  min (Real.smoothTransition (1 / 2)) (1 - Real.smoothTransition (1 / 2))

theorem logCellCentralLower_pos : 0 < logCellCentralLower := by
  exact lt_min (Real.smoothTransition.pos_of_pos (by norm_num))
    (sub_pos.mpr (Real.smoothTransition.lt_one_of_lt_one (by norm_num)))

theorem logCellProfile_nonneg (x : ℝ) : 0 ≤ logCellProfile x :=
  sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

theorem logCellProfile_le_one (x : ℝ) : logCellProfile x ≤ 1 := by
  unfold logCellProfile
  linarith [Real.smoothTransition.le_one (x + 1), Real.smoothTransition.nonneg x]

theorem logCellProfile_zero_outside (x : ℝ) (hx : 1 ≤ |x|) : logCellProfile x = 0 := by
  unfold logCellProfile
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h] at hx
    rw [Real.smoothTransition.one_of_one_le (by linarith), Real.smoothTransition.one_of_one_le hx]
    norm_num
  · rw [abs_of_nonpos h] at hx
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), Real.smoothTransition.zero_of_nonpos h]
    norm_num

theorem logCellProfile_central (x : ℝ) (hx : |x| ≤ 1 / 2) :
    logCellCentralLower ≤ logCellProfile x := by
  have hh := abs_le.mp hx
  unfold logCellCentralLower logCellProfile
  by_cases h : 0 ≤ x
  · rw [Real.smoothTransition.one_of_one_le (x := x + 1) (by linarith)]
    have ht := Real.smoothTransition.monotone hh.2
    exact (min_le_right _ _).trans (sub_le_sub_left ht 1)
  · rw [Real.smoothTransition.zero_of_nonpos (le_of_not_ge h), sub_zero]
    exact (min_le_left _ _).trans (Real.smoothTransition.monotone (by linarith))

theorem logCellProfile_contDiff {n : ℕ∞} : ContDiff ℝ n logCellProfile :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

/-- The two nonzero translates telescope to one on a unit logarithmic cell. -/
theorem logCellProfile_partition (x : ℝ) (hlo : 0 ≤ x) (hhi : x ≤ 1) :
    logCellProfile x + logCellProfile (x - 1) = 1 := by
  unfold logCellProfile
  rw [Real.smoothTransition.one_of_one_le (x := x + 1) (by linarith),
    Real.smoothTransition.zero_of_nonpos (x := x - 1) (by linarith), sub_add_cancel]
  ring

/-- The full integer partition of unity specified for the logarithmic cells.
Only the two translates adjacent to `floor x` can be nonzero. -/
theorem logCellProfile_partition_unity (x : ℝ) :
    (∑' n : ℤ, logCellProfile (x - n)) = 1 := by
  let z := ⌊x⌋
  have hzlo : (z : ℝ) ≤ x := Int.floor_le x
  have hzhi : x < (z : ℝ) + 1 := Int.lt_floor_add_one x
  have hzero (n : ℤ) (hn : n ∉ ({z, z + 1} : Finset ℤ)) :
      logCellProfile (x - n) = 0 := by
    have hne : n ≠ z ∧ n ≠ z + 1 := by simpa only [Finset.mem_insert,
      Finset.mem_singleton, not_or] using hn
    apply logCellProfile_zero_outside
    by_cases hle : n ≤ z
    · have hi : n + 1 ≤ z := by omega
      have hr : (n : ℝ) + 1 ≤ z := by exact_mod_cast hi
      exact (show (1 : ℝ) ≤ x - n by linarith).trans (le_abs_self _)
    · have hi : z + 2 ≤ n := by omega
      have hr : (z : ℝ) + 2 ≤ n := by exact_mod_cast hi
      exact (show (1 : ℝ) ≤ -(x - n) by linarith).trans (neg_le_abs _)
  rw [tsum_eq_sum hzero, Finset.sum_pair (by omega : z ≠ z + 1)]
  have hp := logCellProfile_partition (x - z) (by linarith) (by linarith)
  convert hp using 1
  rw [Int.cast_add, Int.cast_one]
  congr 2
  ring

theorem logCellProfile_compactSupport : HasCompactSupport logCellProfile := by
  apply HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc
  intro x hx
  apply logCellProfile_zero_outside
  by_contra h
  have hh := abs_lt.mp (lt_of_not_ge h)
  exact hx ⟨by linarith, by linarith⟩

/-- One fixed finite Lipschitz constant supplies every later variation bound. -/
theorem logCellProfile_lipschitz : ∃ D : ℝ, 0 ≤ D ∧
    ∀ x y, |logCellProfile x - logCellProfile y| ≤ D * |x - y| := by
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (𝕂 := ℝ) logCellProfile_compactSupport
    (logCellProfile_contDiff (n := 1)) (by norm_num)
  refine ⟨D, D.coe_nonneg, ?_⟩
  intro x y
  simpa only [Real.dist_eq] using hD.dist_le_mul x y

/-- The fixed profile discharges the remaining bump premises in the
smooth giant normalizer estimate. -/
theorem PublishedProgressionInput.logCellProfile_normalizer_rate
    (P : PublishedProgressionInput) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ G : ℝ,
      2 ≤ G → Real.exp ((39 / 10000 : ℝ) * L) ≤ G - 1 / 2 →
      G ≤ Real.exp (C * L) →
      Real.exp (-(C + 1 / 10) * L) ≤
        smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
      smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (C + 1 / 10) * L ∧
      (∑ p : smoothGiantPrimeRange G,
        smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G p) = 1 :=
  P.smoothGiant_normalizer_rate C logCellCentralLower logCellCentralLower_pos
    logCellProfile logCellProfile_nonneg logCellProfile_central

end Ostmann

end OAI
