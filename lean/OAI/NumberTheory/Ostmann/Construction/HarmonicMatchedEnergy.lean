import OAI.NumberTheory.Ostmann.Construction.MatchedDiagonalEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSymmetrization

namespace OAI

/-! # The matched diagonal bound for the actual harmonic tuple laws -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem harmonic_tuple_point_of_window {n : ℕ} (P : Finset ℕ)
    (Q : Fin n → Finset ℕ) (x : Fin n → P) (C X : ℝ)
    (hX : 0 < X) (hC : (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ≤ C)
    (hprod : X ≤ ∏ i, (x i : ℝ)) :
    productPrior (fun i => primeSubsetPrior P (Q i)) x ≤ C * X⁻¹ := by
  have hC0 : 0 ≤ C := (show 0 ≤ ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ by positivity).trans hC
  apply (harmonic_product_point_bound P Q x).trans
  exact mul_le_mul hC (inv_anti₀ hX hprod) (by positivity) hC0

theorem harmonic_matched_diagonal_energy {n : ℕ} (P : Finset ℕ)
    (Q R : Fin n → Finset ℕ) (e : Equiv.Perm (Fin n))
    (W Z θ : (Fin n → P) → ℂ) (C X : ℝ) (hC : 0 ≤ C) (hX : 0 < X)
    (hQ : (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ≤ C)
    (hR : (∏ i, (∑ p ∈ R i, (p : ℝ)⁻¹)⁻¹) ≤ C)
    (hθ : ∀ x, ‖θ x‖ ≤ 1)
    (hwindow : ∀ x, W x ≠ 0 → Z (permuteBulk e x) ≠ 0 → X ≤ ∏ i, (x i : ℝ)) :
    ‖∑ x, ((productPrior (fun i => primeSubsetPrior P (Q i)) x *
        productPrior (fun i => primeSubsetPrior P (R i)) (permuteBulk e x) : ℝ) : ℂ) *
        W x * conj (Z (permuteBulk e x)) * θ x‖ ≤
      (C * X⁻¹) / 2 *
        ((∑ x, productPrior (fun i => primeSubsetPrior P (Q i)) x * ‖W x‖ ^ 2) +
          ∑ x, productPrior (fun i => primeSubsetPrior P (R i)) x * ‖Z x‖ ^ 2) := by
  apply matched_diagonal_energy (bulkArrayEquiv (A := P) e) _ _ W Z θ (C * X⁻¹)
    (by positivity)
    (fun x => productPrior_nonneg _ (fun i p => primeSubsetPrior_nonneg P (Q i) p) x)
    (fun x => productPrior_nonneg _ (fun i p => primeSubsetPrior_nonneg P (R i) p) x) hθ
  intro x hW hZ
  have hx := hwindow x hW hZ
  refine ⟨harmonic_tuple_point_of_window P Q x C X hX hQ hx, ?_⟩
  apply harmonic_tuple_point_of_window P R (permuteBulk e x) C X hX hR
  rw [bulk_value_product_permute (fun p : P => (p : ℝ)) e x]
  exact hx

end Ostmann

end OAI
