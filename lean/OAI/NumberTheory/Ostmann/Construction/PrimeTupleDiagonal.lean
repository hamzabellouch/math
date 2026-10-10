import OAI.NumberTheory.Ostmann.Construction.PrimeTupleFiber
import OAI.NumberTheory.Ostmann.Arithmetic.MovingDiagonalEnergy

namespace OAI

/-! # The actual prime/frequency diagonal under mixed original priors -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def distinctTuplePrior {n : ℕ} (P : Finset ℕ)
    (μ : Fin n → P → ℝ) (x : Fin n → P) : ℝ :=
  if Function.Injective x then productPrior μ x else 0

theorem distinctTuplePrior_nonneg {n : ℕ} (P : Finset ℕ)
    (μ : Fin n → P → ℝ) (hμ : ∀ i p, 0 ≤ μ i p) (x : Fin n → P) :
    0 ≤ distinctTuplePrior P μ x := by
  unfold distinctTuplePrior
  split_ifs
  · exact productPrior_nonneg μ hμ x
  · rfl

/-- This is the quantitative counterpart mass for the exact diagonal key.
The distinctness mask discards tuples, without renormalizing any marginal. -/
theorem distinctTuplePrior_key_mass {n : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (μ : Fin n → P → ℝ) (C : Fin n → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (p : P), (p : ℝ) * μ i p ≤ C i) (V : ℕ) (k : ℕ × ℤ) :
    (∑ a : (Fin n → P) × transferFrequencyRange V,
      if ((∏ i, (a.1 i : ℕ)), (a.2 : ℤ)) = k then distinctTuplePrior P μ a.1 else 0) ≤
      (n.factorial : ℝ) * (∏ i, C i) * (k.1 : ℝ)⁻¹ := by
  rcases k with ⟨M, s⟩
  rw [Fintype.sum_prod_type]
  convert prime_tuple_prior_frequency_mass P hP μ C hμ hC hbound V M s using 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro v _
  simp only [distinctTuplePrior, Prod.mk.injEq]
  by_cases hi : Function.Injective x <;>
    by_cases hp : (∏ i, (x i : ℕ)) = M <;>
    by_cases hv : (v : ℤ) = s <;> simp only [hi, hp, hv, and_self, and_false, false_and,
      ite_true, ite_false]

/-- The Section 7 diagonal with the actual regular Fourier multiplier.
It pays a single factorial counterpart cost and keeps the exact one-sided
energy, rather than taking absolute values of the ungrouped pair terms. -/
theorem prime_tuple_pivot_diagonal_bound {n : ℕ}
    (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)] (hP : ∀ p ∈ P, p.Prime)
    (μ : Fin n → P → ℝ) (C : Fin n → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (p : P), (p : ℝ) * μ i p ≤ C i)
    (V M : ℕ) (hlarge : ∀ p : P, V < (p : ℕ))
    (g : ∀ q : ℕ, ZMod q → ℂ)
    (W : ((Fin n → P) × transferFrequencyRange V) → ℂ)
    (hzero : ∀ x, W (x, ⟨0, by simp [transferFrequencyRange]⟩) = 0) :
    (pivotDiagonal (fun a : (Fin n → P) × transferFrequencyRange V => ∏ i, (a.1 i : ℕ))
      (fun a => (a.2 : ℤ))
      (fun a => (distinctTuplePrior P μ a.1 : ℂ) * W a *
        movingRegularTransform (fun i => (a.1 i : ℕ)) (fun i => g (a.1 i)) M a.2)).re ≤
      ∑ a : (Fin n → P) × transferFrequencyRange V,
        distinctTuplePrior P μ a.1 *
          ((n.factorial : ℝ) * (∏ i, C i) * (((∏ i, (a.1 i : ℕ)) : ℕ) : ℝ)⁻¹) *
          ‖W a * primeProductTransform g M (∏ i, (a.1 i : ℕ)) a.2‖ ^ 2 := by
  let p := fun a : (Fin n → P) × transferFrequencyRange V => fun i => (a.1 i : ℕ)
  let : ∀ a i, Fact (p a i).Prime := fun a i => ⟨hP (a.1 i) (a.1 i).property⟩
  apply moving_regular_pivot_diagonal_le p g M (fun a => (a.2 : ℤ))
    (fun a => distinctTuplePrior P μ a.1) W
    (fun k => (n.factorial : ℝ) * (∏ i, C i) * (k.1 : ℝ)⁻¹)
    (fun a => distinctTuplePrior_nonneg P μ hμ a.1)
  · intro a ha i j hij
    by_cases hx : Function.Injective a.1
    · exact hx (Subtype.ext hij)
    · exact False.elim (ha (by simp only [distinctTuplePrior, hx, ite_false,
        Complex.ofReal_zero, zero_mul]))
  · intro a ha hz
    have he : a.2 = (⟨0, by simp [transferFrequencyRange]⟩ : transferFrequencyRange V) :=
      Subtype.ext hz
    have hwa : W a = 0 := by
      have hpair : a = (a.1, (⟨0, by simp [transferFrequencyRange]⟩ : transferFrequencyRange V)) :=
        Prod.ext rfl he
      rw [hpair]
      exact hzero _
    exact ha (by rw [hwa, mul_zero])
  · intro a _ i
    exact ((mem_transferFrequencyRange V a.2).mp a.2.property).trans_lt (hlarge (a.1 i))
  · exact distinctTuplePrior_key_mass P hP μ C hμ hC hbound V

end Ostmann

end OAI
