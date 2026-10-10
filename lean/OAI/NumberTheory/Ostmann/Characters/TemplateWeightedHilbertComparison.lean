import OAI.NumberTheory.Ostmann.Characters.FactorialContradictionHilbert
import OAI.NumberTheory.Ostmann.Characters.TemplateWeightedHilbert

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.TemplateWeightedHilbert
open Construction
variable {Ω R I : Type*} [Fintype Ω] [Fintype R] [Fintype I]

theorem weighted_permutation_comparison (μ : FinitePrior Ω)
    (f : I → Ω → R → ℂ) (η : ℂ) {D e : ℝ} (he : 0 ≤ e)
    (hmean : ∀ i, μ.cmean (fun ω => ∑ r, f i ω r) = η)
    (hdiag : ∀ i, μ.mean (fun ω => ∑ r, ‖f i ω r‖ ^ 2) ≤ D)
    (hoff : ∀ i j, i ≠ j →
      ‖μ.cmean (fun ω => ∑ r, conj (f i ω r) * f j ω r)‖ ≤ e) :
    (Fintype.card I : ℝ) ^ 2 * ‖η‖ ^ 2 ≤ (Fintype.card R : ℝ) *
      ((Fintype.card I : ℝ) * D + (Fintype.card I : ℝ) ^ 2 * e) := by
  have h := permutation_comparison (fun i => vector μ (f i)) (reference μ) η he
    (fun i => (reference_inner μ (f i)).trans (hmean i))
    (fun i => (vector_norm_sq μ (f i)).trans_le (hdiag i))
    (fun i j hij => by rw [vector_inner]; exact hoff i j hij)
  simpa only [reference_norm_sq] using h

theorem weighted_parity_permutation_comparison (n m : ℕ) (μ : FinitePrior Ω)
    (f : ParityReassignments n m → Ω → R → ℂ) (η : ℂ) {D e : ℝ} (he : 0 ≤ e)
    (hmean : ∀ i, μ.cmean (fun ω => ∑ r, f i ω r) = η)
    (hdiag : ∀ i, μ.mean (fun ω => ∑ r, ‖f i ω r‖ ^ 2) ≤ D)
    (hoff : ∀ i j, i ≠ j →
      ‖μ.cmean (fun ω => ∑ r, conj (f i ω r) * f j ω r)‖ ≤ e) :
    ‖η‖ ^ 2 ≤ (Fintype.card R : ℝ) * (D / (factorialCount n m : ℝ) + e) := by
  have h := parity_permutation_comparison n m (fun i => vector μ (f i))
    (reference μ) η he
    (fun i => (reference_inner μ (f i)).trans (hmean i))
    (fun i => (vector_norm_sq μ (f i)).trans_le (hdiag i))
    (fun i j hij => by rw [vector_inner]; exact hoff i j hij)
  simpa only [reference_norm_sq] using h

theorem weighted_parity_family_impossible (n m : ℕ) (B v C K c α L : ℝ)
    (hK : 0 ≤ K)
    (hcomparison :
      2 * Real.exp (v * factorialMass n m) *
        (Real.exp (C * factorialMass n m) / (factorialCount n m : ℝ) +
          K * Real.exp (-c * Real.exp (α * L))) <
      Real.exp (-2 * B * factorialMass n m))
    (μ : FinitePrior Ω) (f : ParityReassignments n m → Ω → R → ℂ) (η : ℂ)
    (hmean : ∀ i, μ.cmean (fun ω => ∑ r, f i ω r) = η)
    (hamp : Real.exp (-B * factorialMass n m) ≤ ‖η‖)
    (hroots : (Fintype.card R : ℝ) ≤ 2 * Real.exp (v * factorialMass n m))
    (hdiag : ∀ i, μ.mean (fun ω => ∑ r, ‖f i ω r‖ ^ 2) ≤
      Real.exp (C * factorialMass n m))
    (hoff : ∀ i j, i ≠ j →
      ‖μ.cmean (fun ω => ∑ r, conj (f i ω r) * f j ω r)‖ ≤
        K * Real.exp (-c * Real.exp (α * L))) : False := by
  exact parity_family_impossible n m B v C K c α L hK hcomparison
    (fun i => vector μ (f i)) (reference μ) η
    (fun i => (reference_inner μ (f i)).trans (hmean i)) hamp
    ((reference_norm_sq μ).trans_le hroots)
    (fun i => (vector_norm_sq μ (f i)).trans_le (hdiag i))
    (fun i j hij => by rw [vector_inner]; exact hoff i j hij)

end Ostmann.Characters.TemplateWeightedHilbert

end

end OAI
