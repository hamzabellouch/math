import Mathlib

namespace OAI

section
section
namespace MetricKMedian
open Finset

theorem rational_bracket (B : Finset ℚ) (r : ℝ) (lo hi : ℚ)
    (hlo : lo ∈ B) (hhi : hi ∈ B) (hlor : (lo:ℝ) < r) (hrhi : r < (hi:ℝ))
    (hnot : ∀ q ∈ B, (q:ℝ) ≠ r) :
    ∃ a ∈ B, ∃ b ∈ B, (a:ℝ) < r ∧ r < (b:ℝ) ∧
      ∀ q ∈ B, q ≤ a ∨ b ≤ q := by
  classical
  let A : Finset ℚ := B.filter (fun q : ℚ => (q:ℝ) < r)
  let C : Finset ℚ := B.filter (fun q : ℚ => r < (q:ℝ))
  have hA : A.Nonempty := ⟨lo,mem_filter.mpr ⟨hlo,hlor⟩⟩
  have hC : C.Nonempty := ⟨hi,mem_filter.mpr ⟨hhi,hrhi⟩⟩
  let a := A.max' hA
  let b := C.min' hC
  have ha := mem_filter.mp (max'_mem A hA)
  have hb := mem_filter.mp (min'_mem C hC)
  refine ⟨a,ha.1,b,hb.1,ha.2,hb.2,?_⟩
  intro q hq
  rcases lt_or_gt_of_ne (hnot q hq) with hqlo | hqhi
  · exact Or.inl (le_max' A q (mem_filter.mpr ⟨hq,hqlo⟩))
  · exact Or.inr (min'_le C q (mem_filter.mpr ⟨hq,hqhi⟩))

theorem same_interval_cuts (B : Finset ℚ) (a b : ℚ)
    (hgap : ∀ q ∈ B, q ≤ a ∨ b ≤ q) (x y : ℝ)
    (hx : (a:ℝ) < x ∧ x < (b:ℝ)) (hy : (a:ℝ) < y ∧ y < (b:ℝ)) :
    ∀ q ∈ B, (x ≤ (q:ℝ) ↔ y ≤ (q:ℝ)) ∧ ((q:ℝ) ≤ x ↔ (q:ℝ) ≤ y) := by
  intro q hq
  rcases hgap q hq with hq | hq
  · have hq' : (q:ℝ) ≤ a := by exact_mod_cast hq
    exact ⟨iff_of_false (not_le_of_gt (hq'.trans_lt hx.1))
      (not_le_of_gt (hq'.trans_lt hy.1)),iff_of_true (hq'.trans hx.1.le) (hq'.trans hy.1.le)⟩
  · have hq' : (b:ℝ) ≤ q := by exact_mod_cast hq
    exact ⟨iff_of_true (hx.2.le.trans hq') (hy.2.le.trans hq'),
      iff_of_false (not_le_of_gt (hx.2.trans_le hq')) (not_le_of_gt (hy.2.trans_le hq'))⟩

end MetricKMedian
end
end

end OAI
