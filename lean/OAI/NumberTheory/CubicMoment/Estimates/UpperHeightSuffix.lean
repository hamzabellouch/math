import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailHeightPrefix

namespace OAI

/-! The upper height segment is one aligned full tail, starting strictly
above its cutoff unless the segment is empty. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma geometricHeight_filtered_suffix (f : ℝ → ℂ) {H T : ℝ}
    (hH : 0 < H) (hT : 0 < T) (V : ℝ) :
    ∃ j ≤ heightWindowCount H T,
      (j < heightWindowCount H T → V < T*(3/2:ℝ)^j) ∧
      (∑ s ∈ Finset.range (heightWindowCount H T),
        if V < T*(3/2:ℝ)^s then f (T*(3/2:ℝ)^s) else 0) =
        ∑ s ∈ Finset.range (heightWindowCount H (T*(3/2:ℝ)^j)),
          f ((T*(3/2:ℝ)^j)*(3/2:ℝ)^s) := by
  obtain ⟨j,hj,he⟩ := initial_filter_range (p := fun s => T*(3/2:ℝ)^s ≤ V)
    (fun {i j} hij hV => (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3/2) hij) hT.le).trans hV)
    (heightWindowCount H T)
  refine ⟨j,hj,?_,?_⟩
  · intro hjN
    by_contra hn
    have hm : j ∈ (Finset.range (heightWindowCount H T)).filter
        (fun s => T*(3/2:ℝ)^s ≤ V) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjN,le_of_not_gt hn⟩
    rw [he] at hm
    exact (lt_irrefl j) (Finset.mem_range.mp hm)
  · have hprefix : (∑ s ∈ Finset.range (heightWindowCount H T),
        if T*(3/2:ℝ)^s ≤ V then f (T*(3/2:ℝ)^s) else 0) =
        (∑ s ∈ Finset.range (heightWindowCount H T), f (T*(3/2:ℝ)^s))-
          ∑ s ∈ Finset.range (heightWindowCount H (T*(3/2:ℝ)^j)),
            f ((T*(3/2:ℝ)^j)*(3/2:ℝ)^s) := by
      rw [←Finset.sum_filter,he]
      exact geometricHeight_prefix f hH hT hj
    have hsum : (∑ s ∈ Finset.range (heightWindowCount H T),
        if T*(3/2:ℝ)^s ≤ V then f (T*(3/2:ℝ)^s) else 0)+
        (∑ s ∈ Finset.range (heightWindowCount H T),
          if V < T*(3/2:ℝ)^s then f (T*(3/2:ℝ)^s) else 0) =
        ∑ s ∈ Finset.range (heightWindowCount H T), f (T*(3/2:ℝ)^s) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : T*(3/2:ℝ)^s ≤ V
      · simp only [hs,not_lt.mpr hs,ite_true,ite_false,add_zero]
      · simp only [hs,lt_of_not_ge hs,ite_true,ite_false,zero_add]
    rw [hprefix] at hsum
    linear_combination hsum

end CubicFirstMoment

end

end OAI
