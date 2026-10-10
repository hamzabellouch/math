import Mathlib.Data.Int.Interval
import OAI.NumberTheory.Ostmann.Construction.LocalSmoothGiantSelection

namespace OAI

/-! # Complete integer cell families around a real prime block -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def logBlockCenters (lo hi : ℝ) : Finset ℤ :=
  Finset.Icc (⌊lo⌋ - 1) (⌈hi⌉ + 1)

theorem logBlockCenters_bounds (lo hi : ℝ) {n : ℤ} (hn : n ∈ logBlockCenters lo hi) :
    lo - 2 ≤ n ∧ (n : ℝ) ≤ hi + 2 := by
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
  have hl : ((⌊lo⌋ : ℤ) : ℝ) - 1 ≤ n := by exact_mod_cast hnlo
  have hh : (n : ℝ) ≤ ((⌈hi⌉ : ℤ) : ℝ) + 1 := by exact_mod_cast hnhi
  constructor <;> linarith [Int.lt_floor_add_one lo, Int.ceil_lt_add_one hi]

theorem logCellFamilyWeight_le_one (C : Finset ℤ) (p : ℕ) :
    logCellFamilyWeight C p ≤ 1 := by
  let D : Finset ℤ := {⌊Real.log p⌋, ⌊Real.log p⌋ + 1}
  have hs : logCellFamilyWeight C p =
      ∑ n ∈ C ∩ D, logCellProfile (Real.log p - n) := by
    symm
    apply Finset.sum_subset (Finset.inter_subset_left)
    intro n hn hnot
    apply logCellProfile_zero_off_centers
    intro hm
    exact hnot (Finset.mem_inter.mpr ⟨hn, hm⟩)
  rw [hs]
  have hh : (∑ n ∈ C ∩ D, logCellProfile (Real.log p - n)) ≤
      ∑ n ∈ D, logCellProfile (Real.log p - n) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun n _ _ => logCellProfile_nonneg _)
  apply hh.trans_eq
  rw [← logCellProfile_partition_unity (Real.log p)]
  symm
  exact tsum_eq_sum fun n hn => logCellProfile_zero_off_centers (Real.log p) n hn

theorem logBlockCenters_partition (lo hi : ℝ) (p : ℕ)
    (hlo : lo ≤ Real.log p) (hhi : Real.log p ≤ hi) :
    logCellFamilyWeight (logBlockCenters lo hi) p = 1 := by
  rw [logCellFamilyWeight, ← logCellProfile_partition_unity (Real.log p)]
  symm
  apply tsum_eq_sum
  intro n hn
  apply logCellProfile_zero_off_centers
  intro hmem
  apply hn
  apply Finset.mem_Icc.mpr
  have hf : ⌊lo⌋ ≤ ⌊Real.log p⌋ := Int.floor_mono hlo
  have hc : ⌊Real.log p⌋ ≤ ⌈hi⌉ :=
    (Int.floor_le_floor hhi).trans (Int.floor_le_ceil hi)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl <;> omega

theorem logBlockCenters_weight_zero (lo hi : ℝ) (p : ℕ)
    (hout : Real.log p < lo - 3 ∨ hi + 3 < Real.log p) :
    logCellFamilyWeight (logBlockCenters lo hi) p = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  obtain ⟨hl, hh⟩ := logBlockCenters_bounds lo hi hn
  apply logCellProfile_zero_outside
  rcases hout with hout | hout
  · exact (show 1 ≤ - (Real.log p - n) by linarith).trans (neg_le_abs _)
  · exact (show 1 ≤ Real.log p - n by linarith).trans (le_abs_self _)

/-- One ambient giant container contains every complete cell in the block. -/
theorem logBlockCenters_full_cells (lo hi : ℝ) :
    ∀ n ∈ logBlockCenters lo hi,
      smoothGiantPrimeRange n ⊆ smoothGiantPrimeRange (hi + 2) := by
  intro n hn p hp
  obtain ⟨hpI, hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp1, hpU⟩ := Finset.mem_Icc.mp hpI
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hp1, hpU.trans ?_⟩, hprime⟩
  exact Nat.ceil_mono (Real.exp_le_exp.mpr (by linarith [(logBlockCenters_bounds lo hi hn).2]))

end Ostmann

end OAI
