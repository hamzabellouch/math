import OAI.NumberTheory.Ostmann.Characters.MixedExternalAverage
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleDiagonalExpansion

namespace OAI

/-! # Retaining both complete smooth cells in the mixed external average -/

namespace Ostmann
open scoped Classical BigOperators

private theorem primeInterval_function_add (u v : ℝ) (F H : ℝ → ℂ) :
    complexPrimeInterval 1 0 u v (fun x => F x + H x) =
      complexPrimeInterval 1 0 u v F + complexPrimeInterval 1 0 u v H := by
  unfold complexPrimeInterval
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

theorem mixedExternalAverage_left_add {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v t r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (huv : u ≤ v) (hvt : v ≤ t) :
    mixedExternalAverage ν N u v r w center F + mixedExternalAverage ν N v t r w center F =
      mixedExternalAverage ν N u t r w center F := by
  unfold mixedExternalAverage
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [← mul_add, ← primeInterval_function_add]
  congr 1
  apply congrArg (complexPrimeInterval 1 0 r w)
  funext z
  exact complexIntegerInterval_add 1 0 u v t center _ huv hvt

theorem mixedExternalAverage_right_add {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r t w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (hrt : r ≤ t) (htw : t ≤ w) :
    mixedExternalAverage ν N u v r t center F + mixedExternalAverage ν N u v t w center F =
      mixedExternalAverage ν N u v r w center F := by
  unfold mixedExternalAverage
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [← mul_add, complexPrimeInterval_add 1 0 r t w _ hrt htw]

theorem mixedExternalAverage_four_cells {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (G H center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N (G - 1) (G + 1) (H - 1) (H + 1) center F =
      (mixedExternalAverage ν N (G - 1) G (H - 1) H center F +
        mixedExternalAverage ν N G (G + 1) (H - 1) H center F) +
      (mixedExternalAverage ν N (G - 1) G H (H + 1) center F +
        mixedExternalAverage ν N G (G + 1) H (H + 1) center F) := by
  rw [mixedExternalAverage_left_add ν N (G - 1) G (G + 1) (H - 1) H center F
      (by linarith) (by linarith),
    mixedExternalAverage_left_add ν N (G - 1) G (G + 1) H (H + 1) center F
      (by linarith) (by linarith),
    mixedExternalAverage_right_add ν N (G - 1) (G + 1) (H - 1) H (H + 1) center F
      (by linarith) (by linarith)]

theorem mixedExternalAverage_full_cell_bound {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (G H center E : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (h : ∀ i j : Bool, ‖mixedExternalAverage ν N
      (if i then G else G - 1) ((if i then G else G - 1) + 1)
      (if j then H else H - 1) ((if j then H else H - 1) + 1) center F‖ ≤ E) :
    ‖mixedExternalAverage ν N (G - 1) (G + 1) (H - 1) (H + 1) center F‖ ≤ 4 * E := by
  rw [mixedExternalAverage_four_cells]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans
  have h00 := h false false
  have h10 := h true false
  have h01 := h false true
  have h11 := h true true
  simp only [Bool.false_eq_true, ite_false, ite_true, sub_add_cancel] at h00 h10 h01 h11
  linarith

end Ostmann

end OAI
