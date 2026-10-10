import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteLaplaceDensity

namespace OAI

/-! # Inverse-square summability from a three-halves counting bound -/

namespace Ostmann

open scoped Classical BigOperators

/-- Sorting by height converts the counting bound into a convergent 4/3-series. -/
theorem finite_exp_three_halves_sum {ι : Type*} (S : Finset ι)
    (y : ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hy : ∀ i ∈ S, 0 ≤ y i)
    (hc : ∀ t : ℝ, 0 ≤ t →
      ((S.filter (fun i => y i ≤ t)).card : ℝ) ≤ B * Real.exp ((3 / 2) * t)) :
    (∑ i ∈ S, Real.exp (-2 * y i)) ≤ B ^ (4 / 3 : ℝ) *
      ∑ j ∈ Finset.range S.card, ((j + 1 : ℕ) : ℝ) ^ (-4 / 3 : ℝ) := by
  revert hy hc
  refine Finset.strongInductionOn S ?_
  intro S ih hy hc
  by_cases hn : S.Nonempty
  · obtain ⟨i, hi, hmax⟩ := S.exists_max_image y hn
    have hf : S.filter (fun j => y j ≤ y i) = S := Finset.filter_eq_self.mpr hmax
    have hcard := hc (y i) (hy i hi)
    rw [hf] at hcard
    have hn0 : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hn
    have hm := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg (-((3 / 2) * y i)))
    have he : Real.exp ((3 / 2) * y i) * Real.exp (-((3 / 2) * y i)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [mul_assoc, he, mul_one] at hm
    have hd : Real.exp (-((3 / 2) * y i)) ≤ B / S.card := by
      apply (le_div_iff₀ hn0).mpr
      simpa only [mul_comm] using hm
    have hpoint : Real.exp (-2 * y i) ≤ B ^ (4 / 3 : ℝ) * (S.card : ℝ) ^ (-4 / 3 : ℝ) := by
      have hh := Real.rpow_le_rpow (Real.exp_nonneg _) hd (by norm_num : (0 : ℝ) ≤ 4 / 3)
      rw [← Real.exp_mul, Real.div_rpow hB hn0.le, div_eq_mul_inv] at hh
      convert hh using 1
      · congr 1; ring
      · rw [show (-4 / 3 : ℝ) = -(4 / 3) by ring, Real.rpow_neg hn0.le]
        rfl
    have hrest := ih (S.erase i) (Finset.erase_ssubset hi)
      (fun j hj => hy j (Finset.mem_of_mem_erase hj))
      (fun t ht => (show (((S.erase i).filter (fun j => y j ≤ t)).card : ℝ) ≤
        (S.filter (fun j => y j ≤ t)).card from by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))).trans
          (hc t ht))
    have hsize : (S.erase i).card + 1 = S.card := Finset.card_erase_add_one hi
    rw [← Finset.sum_erase_add S (fun i => Real.exp (-2 * y i)) hi]
    rw [← hsize, Finset.sum_range_succ, mul_add]
    exact add_le_add hrest (by simpa only [hsize] using hpoint)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty, Finset.card_empty, Finset.range_zero, mul_zero, le_refl]

end Ostmann

end OAI
