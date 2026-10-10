import OAI.NumberTheory.Ostmann.Characters.PivotIntegerTransfer
import OAI.NumberTheory.Ostmann.Construction.DiagonalTransfer

namespace OAI

/-! # Grouping the actual pivot row before the integer extension -/

namespace Ostmann

open scoped BigOperators Classical

theorem pivot_residue_grouping {A U : Type*} [Fintype A] [Fintype U]
    (key : A → U) (row : U → ℂ) (c : A → ℂ) :
    (∑ a, row (key a) * c a) = ∑ u, row u * groupedCoefficient key c u := by
  symm
  unfold groupedCoefficient
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem pivot_grouped_integer_transfer {A : ℕ → Type*} [∀ M, Fintype (A M)]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (Q : Fin n → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (S : Finset (Fin n → P)) (hS : ∀ x ∈ S, Function.Injective x)
    (T : Finset ℕ) (hT : ∀ x ∈ S, (∏ i, (x i : ℕ)) ∈ T)
    (row : ∀ x : Fin n → P, Fin (∏ i, (x i : ℕ)) → ℂ)
    (hrow : ∀ x ∈ S, ∀ u, ‖row x u‖ ≤ 1)
    (key : ∀ M : ℕ, A M → Fin M) (c : ∀ M, A M → ℂ) :
    ‖∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
        ∑ a, row x (key (∏ i, (x i : ℕ)) a) * c (∏ i, (x i : ℕ)) a‖ ^ 2 ≤
      ((n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) *
        ∑ M ∈ T, ∑ u, ‖groupedCoefficient (key M) (c M) u‖ ^ 2 := by
  have he : (∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
      ∑ a, row x (key (∏ i, (x i : ℕ)) a) * c (∏ i, (x i : ℕ)) a) =
      ∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
        ∑ u, row x u * groupedCoefficient (key (∏ i, (x i : ℕ))) (c (∏ i, (x i : ℕ))) u := by
    apply Finset.sum_congr rfl
    intro x _
    rw [pivot_residue_grouping (key (∏ i, (x i : ℕ))) (row x) (c (∏ i, (x i : ℕ)))]
  rw [he]
  exact pivot_integer_transfer P hP Q hQP hQ S hS T hT row hrow
    (fun M => groupedCoefficient (key M) (c M))

end Ostmann

end OAI
