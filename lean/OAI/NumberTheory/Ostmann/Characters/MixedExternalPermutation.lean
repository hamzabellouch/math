import OAI.NumberTheory.Ostmann.Characters.MixedExternalAverage

namespace OAI

/-! # Reindexing the original mixed external law by its selected bulk coordinates -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalAverage_selectedBulkSample {B J A : Type*}
    [Fintype B] [Fintype A]
    (slot : J ↪ B) (e : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ) (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N u v r w center
      (fun s y x z => F s (selectedBulkSample slot e y) x z) =
    mixedExternalAverage ν N u v r w center F := by
  unfold mixedExternalAverage
  apply Finset.sum_congr rfl
  intro s _
  exact selectedBulkSample_sum slot e ν hν
    (fun y => complexPrimeInterval 1 0 r w (fun z =>
      complexIntegerInterval 1 0 u v center (fun x => F s.val y x z)))

theorem mixedExternalAverage_relative_pair {B J A : Type*}
    [Fintype B] [Fintype A]
    (slot : J ↪ B) (e f : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (W : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (hW : ∀ e s y x z, W s (selectedBulkSample slot e y) x z = W s y x z) :
    mixedExternalAverage ν N u v r w center
      (fun s y x z =>
        (F s (selectedBulkSample slot e y) x z *
          star (F s (selectedBulkSample slot f y) x z)) * W s y x z) =
    mixedExternalAverage ν N u v r w center
      (fun s y x z =>
        (F s y x z * star (F s (selectedBulkSample slot (f * e⁻¹) y) x z)) * W s y x z) := by
  rw [← mixedExternalAverage_selectedBulkSample slot e⁻¹ ν hν]
  congr 1
  funext s y x z
  rw [hW, ← selectedBulkSample_mul, ← selectedBulkSample_mul]
  simp only [mul_inv_cancel, selectedBulkSample_one]

theorem mixedExternalAverage_pair_swap {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ) (W : ℤ → (B → A) → ℝ → ℝ → ℝ) :
    ‖mixedExternalAverage ν N u v r w center
      (fun s y x z => (F s y x z * star (H s y x z)) * W s y x z)‖ =
    ‖mixedExternalAverage ν N u v r w center
      (fun s y x z => (H s y x z * star (F s y x z)) * W s y x z)‖ := by
  conv_lhs => rw [← norm_star]
  rw [← mixedExternalAverage_star]
  congr 2
  funext s y x z
  simp [mul_comm]

end Ostmann

end OAI
