import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Finite independent priors used for the arithmetic samples -/

namespace Ostmann

open scoped BigOperators

noncomputable def productPrior {A : Type*} {n : ℕ}
    (μ : Fin n → A → ℝ) (x : Fin n → A) : ℝ := ∏ i, μ i (x i)

theorem productPrior_nonneg {A : Type*} {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (x : Fin n → A) :
    0 ≤ productPrior μ x := Finset.prod_nonneg fun i _ => hμ i (x i)

theorem productPrior_mass {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i, ∑ a, μ i a = 1) :
    (∑ x : Fin n → A, productPrior μ x) = 1 := by
  unfold productPrior
  rw [← Fintype.prod_sum]
  simp only [hμ, Finset.prod_const_one]

theorem productPrior_cons {A : Type*} {n : ℕ}
    (μ : Fin (n + 1) → A → ℝ) (a : A) (x : Fin n → A) :
    productPrior μ (Fin.cons a x) = μ 0 a * productPrior (fun i => μ i.succ) x := by
  simp only [productPrior, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Integrate the first sample last, keeping the product prior on all remaining samples. -/
theorem sum_productPrior_cons {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin (n + 1) → A → ℝ) (f : (Fin (n + 1) → A) → ℝ) :
    (∑ v, productPrior μ v * f v) =
      ∑ x : Fin n → A, productPrior (fun i => μ i.succ) x *
        ∑ a : A, μ 0 a * f (Fin.cons a x) := by
  have h := (Fin.consEquiv (fun _ : Fin (n + 1) => A)).sum_comp
    (fun v => productPrior μ v * f v)
  rw [← h, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change productPrior μ (Fin.cons a x) * f (Fin.cons a x) = _
  rw [productPrior_cons]
  ring

end Ostmann

end OAI
