import Mathlib
import OAI.Analysis.IrrationalRotation.Model.PhaseFailure

namespace OAI

namespace Invariant233.ProductPhases

theorem mem_nonzeroIntegerWindow {R : ℝ} {k : ℤ} :
    k ∈ nonzeroIntegerWindow R ↔ k ≠ 0 ∧ |(k : ℝ)| ≤ R := by
  simp only [nonzeroIntegerWindow, Finset.mem_erase, Finset.mem_Icc]
  constructor
  · rintro ⟨hk, hlo, hhi⟩
    refine ⟨hk, abs_le.mpr ⟨?_, Int.le_floor.mp hhi⟩⟩
    have hn : -k ≤ Int.floor R := by omega
    have hh := Int.le_floor.mp hn
    simp only [Int.cast_neg] at hh
    linarith
  · rintro ⟨hk, habs⟩
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    have hn : -k ≤ Int.floor R := Int.le_floor.mpr (by push_cast; linarith)
    exact ⟨hk, by omega, Int.le_floor.mpr hhi⟩

theorem card_nonzeroIntegerWindow {R : ℝ} (hR : 0 ≤ R) :
    ((nonzeroIntegerWindow R).card : ℤ) = 2 * Int.floor R := by
  have hf : 0 ≤ Int.floor R := Int.floor_nonneg.mpr hR
  have hz : (0 : ℤ) ∈ Finset.Icc (-Int.floor R) (Int.floor R) := by
    simp only [Finset.mem_Icc]
    omega
  have he := Finset.card_erase_add_one hz
  have he' : ((nonzeroIntegerWindow R).card : ℤ) + 1 =
      ((Finset.Icc (-Int.floor R) (Int.floor R)).card : ℤ) := by
    exact_mod_cast he
  have hI := Int.card_Icc_of_le (a := -Int.floor R) (b := Int.floor R) (by omega)
  omega

theorem card_nonzeroIntegerWindow_le {R : ℝ} (hR : 0 ≤ R) :
    ((nonzeroIntegerWindow R).card : ℝ) ≤ 2 * R := by
  have he : ((nonzeroIntegerWindow R).card : ℝ) = 2 * (Int.floor R : ℝ) := by
    exact_mod_cast card_nonzeroIntegerWindow hR
  rw [he]
  exact mul_le_mul_of_nonneg_left (Int.floor_le R) (by norm_num)

theorem mem_largePhaseTimes {N R : ℝ} (hN : 0 < N) {k : ℤ} :
    k ∈ largePhaseTimes N R ↔ N / 4 ≤ |(k : ℝ)| ∧ |(k : ℝ)| ≤ R := by
  simp only [largePhaseTimes, Finset.mem_filter, mem_nonzeroIntegerWindow]
  constructor
  · rintro ⟨⟨_, hR⟩, hlo⟩
    exact ⟨hlo, hR⟩
  · rintro ⟨hlo, hR⟩
    refine ⟨⟨?_, hR⟩, hlo⟩
    intro hk
    subst k
    norm_num at hlo
    linarith

theorem card_largePhaseTimes_le {N R : ℝ} (hR : 0 ≤ R) :
    ((largePhaseTimes N R).card : ℝ) ≤ 2 * R := by
  apply le_trans _ (card_nonzeroIntegerWindow_le hR)
  unfold largePhaseTimes
  exact_mod_cast Finset.card_filter_le
    (nonzeroIntegerWindow R) (fun k : ℤ => N / 4 ≤ |(k : ℝ)|)

end Invariant233.ProductPhases

end OAI
