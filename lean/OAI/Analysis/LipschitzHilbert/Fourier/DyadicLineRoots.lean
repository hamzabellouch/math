import OAI.Analysis.LipschitzHilbert.Trees.DyadicLineGrid
import Mathlib.Data.Int.Interval

namespace OAI

/-! Only a controlled total length of root cells meets a bounded interval. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.DyadicLineGrid

theorem index_mono (q k : ℤ) : Monotone (index q k) := by
  intro a b hab
  apply Int.floor_mono
  exact sub_le_sub_right (div_le_div_of_nonneg_right hab (scale_pos k).le) _

def rootBand (q k : ℤ) (a b : ℝ) : Finset ℤ :=
  Finset.Icc (index q k a) (index q k b)

theorem mem_rootBand_of_mem_interval {q k : ℤ} {a b x : ℝ} (hx : x ∈ Icc a b) :
    index q k x ∈ rootBand q k a b := by
  exact Finset.mem_Icc.mpr ⟨index_mono q k hx.1, index_mono q k hx.2⟩

theorem interval_subset_rootBand (q k : ℤ) (a b : ℝ) :
    Icc a b ⊆ ⋃ j ∈ rootBand q k a b, cell q k j := by
  intro x hx
  exact mem_iUnion.mpr ⟨index q k x, mem_iUnion.mpr
    ⟨mem_rootBand_of_mem_interval hx, mem_index_cell q k x⟩⟩

/-- The roots meeting a bounded interval have total length at most the
interval length plus two root lengths. -/
theorem rootBand_total_length (q k : ℤ) {a b : ℝ} (hab : a ≤ b) :
    (∑ j ∈ rootBand q k a b, volume.real (cell q k j)) ≤ b - a + 2 * scale k := by
  have hidx := index_mono q k hab
  have hcardZ : ((rootBand q k a b).card : ℤ) = index q k b + 1 - index q k a :=
    Int.card_Icc_of_le _ _ (by omega)
  have hcard : ((rootBand q k a b).card : ℝ) =
      (index q k b : ℝ) + 1 - index q k a := by exact_mod_cast hcardZ
  simp only [cell_length, Finset.sum_const, nsmul_eq_mul]
  rw [hcard]
  have ha := mem_index_cell q k a
  have hb := mem_index_cell q k b
  change left q k (index q k a) ≤ a ∧ a < left q k (index q k a + 1) at ha
  change left q k (index q k b) ≤ b ∧ b < left q k (index q k b + 1) at hb
  unfold left at ha hb
  push_cast at ha hb
  nlinarith

/-- A largest scale exists within a factor two of any positive requested
length. Applied to `6H`, it gives exactly the source range `[6H,12H)`. -/
theorem exists_root_scale {H : ℝ} (hH : 0 < H) :
    ∃ k : ℤ, 6 * H ≤ scale k ∧ scale k < 12 * H := by
  obtain ⟨n, hn0, hn1⟩ := exists_mem_Ico_zpow
    (show (0 : ℝ) < 6 * H by positivity) (by norm_num : (1 : ℝ) < 2)
  by_cases heq : scale n = 6 * H
  · exact ⟨n, heq.ge, by rw [heq]; linarith⟩
  · refine ⟨n + 1, ?_, ?_⟩
    · exact le_of_lt hn1
    · rw [scale_succ]
      change scale n ≤ 6 * H at hn0
      have hlt := lt_of_le_of_ne hn0 heq
      linarith

end LipschitzHilbert.DyadicLineGrid

end

end OAI
