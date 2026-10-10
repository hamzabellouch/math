import OAI.NumberTheory.Ostmann.Preliminaries.TransferCauchy
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors
import OAI.NumberTheory.Ostmann.Construction.FiniteEnumeration

namespace OAI

/-! # The giant-only prime-to-integer row transfer in Section 7.5

The compensation product stays in the modulus. Only the actual giant prime
is averaged with its smooth harmonic prior, so no tuple-factorial loss occurs.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem moving_prime_row_transfer {A : Type*} [Fintype A]
    (P I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPI : P ⊆ I)
    (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hμmass : ∑ a, μ a = 1)
    (w : ℕ → ℝ) (hw : ∀ p ∈ I, 0 ≤ w p) (Z : ℝ) (hZ : 0 ≤ Z)
    (hmass : ∑ p : P, Z * w p / (p : ℝ) = 1)
    (U : A → ℕ)
    (row : ∀ a, (p : P) → Fin ((p : ℕ) * U a) → ℂ)
    (B : ∀ a p, Fin (p * U a) → ℂ)
    (hrow : ∀ a p, (∑ t, ‖row a p t‖ ^ 2) ≤ (p : ℕ) * (U a : ℝ)) :
    ‖∑ a, (μ a : ℂ) * ∑ p : P, ((Z * w p / (p : ℝ) : ℝ) : ℂ) *
        ∑ t, row a p t * B a p t‖ ^ 2 ≤
      Z * ∑ a, μ a * (U a : ℝ) * ∑ p ∈ I, w p * ∑ t, ‖B a p t‖ ^ 2 := by
  let ν := fun ap : A × P => μ ap.1 * (Z * w ap.2 / (ap.2 : ℝ))
  have hν (ap) : 0 ≤ ν ap :=
    mul_nonneg (hμ ap.1) (div_nonneg (mul_nonneg hZ (hw _ (hPI ap.2.property)))
      (Nat.cast_nonneg _))
  have hνmass : ∑ ap, ν ap = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [ν, ← Finset.mul_sum, hmass, mul_one, hμmass]
  have hh := finite_transfer_row_bound ν hν hνmass
    (fun ap => row ap.1 ap.2) (fun ap => B ap.1 ap.2)
    (fun ap => (ap.2 : ℕ) * (U ap.1 : ℝ)) (fun ap => hrow ap.1 ap.2)
  have hleft : (∑ ap : A × P, (ν ap : ℂ) * ∑ t, row ap.1 ap.2 t * B ap.1 ap.2 t) =
      ∑ a, (μ a : ℂ) * ∑ p : P, ((Z * w p / (p : ℝ) : ℝ) : ℂ) *
        ∑ t, row a p t * B a p t := by
    rw [Fintype.sum_prod_type]
    simp only [ν, Complex.ofReal_mul, Finset.mul_sum, mul_assoc]
  rw [hleft] at hh
  apply hh.trans
  have hcancel (a) (p : P) :
      (Z * w p / (p : ℝ)) * ((p : ℕ) * (U a : ℝ)) = Z * (U a : ℝ) * w p := by
    have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hP _ p.property).ne_zero
    field_simp
  rw [Fintype.sum_prod_type]
  calc
    (∑ a, ∑ p : P, ν (a, p) * ((p : ℕ) * (U a : ℝ) * ∑ t, ‖B a p t‖ ^ 2)) =
        Z * ∑ a, μ a * (U a : ℝ) * ∑ p ∈ P, w p * ∑ t, ‖B a p t‖ ^ 2 := by
      simp only [ν]
      simp_rw [show ∀ a (p : P), μ a * (Z * w p / (p : ℝ)) *
          ((p : ℕ) * (U a : ℝ) * ∑ t, ‖B a p t‖ ^ 2) =
          Z * (μ a * (U a : ℝ) * (w p * ∑ t, ‖B a p t‖ ^ 2)) from fun a p => by
            calc
              _ = μ a * ((Z * w p / (p : ℝ)) * ((p : ℕ) * (U a : ℝ))) *
                  (∑ t, ‖B a p t‖ ^ 2) := by ring
              _ = _ := by rw [hcancel]; ring]
      simp only [← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      simpa only [finite_univ_canonical] using
        (Finset.sum_coe_sort P (fun p => w p * ∑ t, ‖B a p t‖ ^ 2))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hZ
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hμ a) (Nat.cast_nonneg _))
      apply Finset.sum_le_sum_of_subset_of_nonneg hPI
      intro p hp _
      exact mul_nonneg (hw p hp) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end Ostmann

end OAI
