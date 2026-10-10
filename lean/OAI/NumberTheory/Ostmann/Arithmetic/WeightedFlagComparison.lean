import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.BigOperators

namespace OAI

/-! # Weighted error when finitely many arithmetic flags are replaced -/

namespace Ostmann

open scoped BigOperators

/-- A bounded function of finitely many flags changes only on their union of
exceptional events. This estimate retains the original independent weights. -/
theorem weighted_flag_comparison_le {X I : Type*} [Fintype X] [Fintype I]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (f g : X → I → Bool) (bad : I → X → Prop) [∀ i x, Decidable (bad i x)]
    (heq : ∀ x, (∀ i, ¬bad i x) → f x = g x)
    (Ψ : X → (I → Bool) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hΨ : ∀ x v, ‖Ψ x v‖ ≤ B) :
    ‖∑ x, (w x : ℂ) * (Ψ x (f x) - Ψ x (g x))‖ ≤
      2 * B * ∑ i, ∑ x, w x * if bad i x then 1 else 0 := by
  classical
  have hpoint (x : X) : ‖Ψ x (f x) - Ψ x (g x)‖ ≤
      2 * B * ∑ i, if bad i x then (1 : ℝ) else 0 := by
    by_cases hx : ∃ i, bad i x
    · obtain ⟨i, hi⟩ := hx
      have hsum : (1 : ℝ) ≤ ∑ j, if bad j x then 1 else 0 := by
        simpa only [hi, ite_true] using
          (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
            (show (0 : ℝ) ≤ if bad j x then 1 else 0 by split <;> norm_num))
            (Finset.mem_univ i))
      have hn : ‖Ψ x (f x) - Ψ x (g x)‖ ≤ 2 * B :=
        (norm_sub_le _ _).trans (by linarith [hΨ x (f x), hΨ x (g x)])
      exact hn.trans (by nlinarith)
    · have hf : f x = g x := heq x (by simpa only [not_exists] using hx)
      rw [hf, sub_self, norm_zero]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  calc
    _ ≤ ∑ x, ‖(w x : ℂ) * (Ψ x (f x) - Ψ x (g x))‖ := norm_sum_le _ _
    _ = ∑ x, w x * ‖Ψ x (f x) - Ψ x (g x)‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)]
    _ ≤ ∑ x, w x * (2 * B * ∑ i, if bad i x then (1 : ℝ) else 0) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hw x)
    _ = _ := by
      simp only [Finset.mul_sum]
      simp_rw [show ∀ x i, w x * (2 * B * (if bad i x then (1 : ℝ) else 0)) =
        2 * B * (w x * (if bad i x then 1 else 0)) by intros; ring]
      rw [Finset.sum_comm]

end Ostmann

end OAI
