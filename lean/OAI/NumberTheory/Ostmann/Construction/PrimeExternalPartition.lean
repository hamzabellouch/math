import OAI.NumberTheory.Ostmann.Construction.PrimeExternalAverage

namespace OAI

/-! # The full smooth giant cells from their four unit rectangles -/

namespace Ostmann
open scoped Classical BigOperators

private theorem complexPrimeInterval_function_add (u v : ℝ) (F H : ℝ → ℂ) :
    complexPrimeInterval 1 0 u v (fun x => F x + H x) =
      complexPrimeInterval 1 0 u v F + complexPrimeInterval 1 0 u v H := by
  unfold complexPrimeInterval
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

theorem primeExternalAverage_left_add {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v t r w : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (huv : u ≤ v) (hvt : v ≤ t) :
    primeExternalAverage ν N u v r w F + primeExternalAverage ν N v t r w F =
      primeExternalAverage ν N u t r w F := by
  unfold primeExternalAverage
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [← mul_add, ← complexPrimeInterval_function_add]
  congr 1
  apply congrArg (complexPrimeInterval 1 0 r w)
  funext z
  exact complexPrimeInterval_add 1 0 u v t _ huv hvt

theorem primeExternalAverage_right_add {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r s w : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (hrs : r ≤ s) (hsw : s ≤ w) :
    primeExternalAverage ν N u v r s F + primeExternalAverage ν N u v s w F =
      primeExternalAverage ν N u v r w F := by
  unfold primeExternalAverage
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [← mul_add, complexPrimeInterval_add 1 0 r s w _ hrs hsw]

theorem primeExternalAverage_four_cells {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (G H : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    primeExternalAverage ν N (G - 1) (G + 1) (H - 1) (H + 1) F =
      (primeExternalAverage ν N (G - 1) G (H - 1) H F +
        primeExternalAverage ν N G (G + 1) (H - 1) H F) +
      (primeExternalAverage ν N (G - 1) G H (H + 1) F +
        primeExternalAverage ν N G (G + 1) H (H + 1) F) := by
  rw [primeExternalAverage_left_add ν N (G - 1) G (G + 1) (H - 1) H F
      (by linarith) (by linarith),
    primeExternalAverage_left_add ν N (G - 1) G (G + 1) H (H + 1) F
      (by linarith) (by linarith),
    primeExternalAverage_right_add ν N (G - 1) (G + 1) (H - 1) H (H + 1) F
      (by linarith) (by linarith)]

private theorem four_complex_terms_square_le (a b c d : ℂ) (E : ℝ)
    (ha : ‖a‖ ^ 2 ≤ E) (hb : ‖b‖ ^ 2 ≤ E) (hc : ‖c‖ ^ 2 ≤ E) (hd : ‖d‖ ^ 2 ≤ E) :
    ‖(a + b) + (c + d)‖ ^ 2 ≤ 16 * E := by
  have hadd (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    calc
      _ ≤ (‖x‖ + ‖y‖) ^ 2 := by gcongr; exact norm_add_le x y
      _ ≤ _ := by nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have h₁ := hadd a b
  have h₂ := hadd c d
  have h₃ := hadd (a + b) (c + d)
  linarith

/-- The complete pair of width-two cells loses only the fixed factor sixteen
in the squared bound. No boundary primes are removed. -/
theorem primeExternalAverage_full_cell_bound {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (G H E : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (h : ∀ i j : Bool, ‖primeExternalAverage ν N
      (if i then G else G - 1) ((if i then G else G - 1) + 1)
      (if j then H else H - 1) ((if j then H else H - 1) + 1) F‖ ^ 2 ≤ E) :
    ‖primeExternalAverage ν N (G - 1) (G + 1) (H - 1) (H + 1) F‖ ^ 2 ≤ 16 * E := by
  rw [primeExternalAverage_four_cells]
  apply four_complex_terms_square_le
  · simpa using h false false
  · simpa using h true false
  · simpa using h false true
  · simpa using h true true

end Ostmann

end OAI
