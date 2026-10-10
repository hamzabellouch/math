import OAI.MeasureTheory.Falconer.Estimates.PrefixCounting

namespace OAI

/-! A large uniform subset retains mass in every one of its occupied parent
cells. This makes the original profile estimates hereditary after thinning. -/
namespace Falconer.Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem prefix_fiber_local_retention (C S : Finset (CellPath 2)) (a : ℕ)
    (hSC : S ⊆ C) {M A D b d : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hd : 0 ≤ d) (hmass : (C.card:ℝ) ≤ M*(S.card:ℝ))
    (hC : ∀ q ∈ C.image (List.take a), b ≤ ((prefixFiber C a q).card:ℝ) ∧
      ((prefixFiber C a q).card:ℝ) ≤ A*b)
    (hS : ∀ q ∈ S.image (List.take a), d ≤ ((prefixFiber S a q).card:ℝ) ∧
      ((prefixFiber S a q).card:ℝ) ≤ D*d)
    {p : CellPath 2} (hp : p ∈ S.image (List.take a)) :
    ((prefixFiber C a p).card:ℝ) ≤ (A*M*D)*((prefixFiber S a p).card:ℝ) := by
  let B := C.image (List.take a)
  have hBC : p ∈ B := Finset.image_subset_image hSC hp
  have hB : 0 < (B.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨p,hBC⟩)
  have hCsum : (C.card:ℝ) = ∑ q ∈ B, ((prefixFiber C a q).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (List.take a) C
  have hSsum : (S.card:ℝ) = ∑ q ∈ B, ((prefixFiber S a q).card:ℝ) := by
    have hmap : ∀ q ∈ S, q.take a ∈ B := fun q hq => Finset.mem_image_of_mem _ (hSC hq)
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap
  have hCmass : b*(B.card:ℝ) ≤ (C.card:ℝ) := by
    rw [hCsum]
    calc
      _ = ∑ _q ∈ B, b := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun q hq => (hC q hq).1)
  have hSmass : (S.card:ℝ) ≤ (D*d)*(B.card:ℝ) := by
    rw [hSsum]
    calc
      _ ≤ ∑ _q ∈ B, D*d := by
        apply Finset.sum_le_sum
        intro q _
        by_cases hq : (prefixFiber S a q).Nonempty
        · obtain ⟨v,hv⟩ := hq
          obtain ⟨hv,hvq⟩ := Finset.mem_filter.mp hv
          exact (hS q (Finset.mem_image.mpr ⟨v,hv,hvq⟩)).2
        · rw [Finset.not_nonempty_iff_eq_empty.mp hq,Finset.card_empty,Nat.cast_zero]
          exact mul_nonneg hD hd
      _ = _ := by simp; ring
  have hbd : b ≤ M*D*d := by
    apply (mul_le_mul_iff_left₀ hB).1
    calc
      _ ≤ (C.card:ℝ) := hCmass
      _ ≤ M*(S.card:ℝ) := hmass
      _ ≤ M*((D*d)*(B.card:ℝ)) := mul_le_mul_of_nonneg_left hSmass hM
      _ = _ := by ring
  calc
    _ ≤ A*b := (hC p hBC).2
    _ ≤ A*(M*D*d) := mul_le_mul_of_nonneg_left hbd hA
    _ = (A*M*D)*d := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hS p hp).1 (by positivity)

end Falconer.Regularization

end OAI
