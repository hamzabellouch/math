import OAI.NumberTheory.Ostmann.Construction.FiniteProductPrior

namespace OAI

/-! # Separating an internal-prime representative from the other samples -/

namespace Ostmann

open scoped BigOperators

theorem productPrior_insertNth {A : Type*} {n : ℕ}
    (μ : Fin (n + 1) → A → ℝ) (i : Fin (n + 1)) (a : A) (x : Fin n → A) :
    productPrior μ (i.insertNth a x) = μ i a * productPrior (fun j => μ (i.succAbove j)) x := by
  unfold productPrior
  rw [Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

theorem sum_productPrior_insertNth {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin (n + 1) → A → ℝ) (i : Fin (n + 1)) (f : (Fin (n + 1) → A) → ℝ) :
    (∑ v, productPrior μ v * f v) =
      ∑ x : Fin n → A, productPrior (fun j => μ (i.succAbove j)) x *
        ∑ a : A, μ i a * f (i.insertNth a x) := by
  have h := (Fin.insertNthEquiv (fun _ : Fin (n + 1) => A) i).sum_comp
    (fun v => productPrior μ v * f v)
  rw [← h, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change productPrior μ (i.insertNth a x) * f (i.insertNth a x) = _
  rw [productPrior_insertNth]
  ring

end Ostmann

end OAI
