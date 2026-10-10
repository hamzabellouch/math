import OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages

namespace OAI

/-! Positive costs on one progression are controlled by a full interval.
The fixed modulus factor is allowed in the final progression constant. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma uniformAverage_progression_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (a l N : ℕ) (hl : 0 < l) :
    uniformAverage (fun x : Fin N => f (a + l * x.val)) ≤
      (l : ℝ) * uniformAverage (fun y : Fin (l * N) => f (a + y.val)) := by
  by_cases hN : N = 0
  · subst N
    simp [uniformAverage]
  let g : Fin N → Fin (l * N) := fun x => ⟨l * x.val, Nat.mul_lt_mul_of_pos_left x.isLt hl⟩
  have hg : Function.Injective g := by
    intro x y he
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left hl (congrArg Fin.val he)
  have hsum : (∑ x : Fin N, f (a + l * x.val)) ≤
      ∑ y : Fin (l * N), f (a + y.val) := by
    calc
      _ = ∑ y ∈ univ.image g, f (a + y.val) := by
        rw [sum_image]
        exact fun x _ y _ hxy => hg hxy
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun y _ _ => hf _)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl
  simp only [uniformAverage, Fintype.card_fin, Nat.cast_mul]
  calc
    _ ≤ (∑ y : Fin (l * N), f (a + y.val)) / N := div_le_div_of_nonneg_right hsum hNr.le
    _ = _ := by field_simp

end TwoPointCorrelations

end OAI
