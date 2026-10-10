import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticCoincidences
import OAI.NumberTheory.Ostmann.Arithmetic.WeightedFlagComparison

namespace OAI

/-! # Signed replacement of accidental arithmetic flags

After denominators are cleared in §8, coefficient and minor tests are integer
polynomials. Under independent representative priors, replacing their congruence
flags by their rational polynomial-identity flags has the following quantitative
error. The polynomial root and prime-divisor estimates are proved inputs here.
-/

namespace Ostmann

open scoped BigOperators

/-- Use one fixed decision procedure in statements and proofs. -/
noncomputable def arithmeticTestFlag (P : Prop) : Bool := by
  classical
  exact decide P

@[simp] theorem arithmeticTestFlag_of_true {P : Prop} (h : P) : arithmeticTestFlag P = true := by
  simp [arithmeticTestFlag, h]

@[simp] theorem arithmeticTestFlag_of_false {P : Prop} (h : ¬P) : arithmeticTestFlag P = false := by
  simp [arithmeticTestFlag, h]

@[simp] theorem arithmeticTestFlag_eq_true_iff (P : Prop) :
    arithmeticTestFlag P = true ↔ P := by
  classical
  by_cases h : P <;> simp [h]

@[simp] theorem arithmeticTestFlag_eq_false_iff (P : Prop) :
    arithmeticTestFlag P = false ↔ ¬P := by
  classical
  by_cases h : P <;> simp [h]

/-- The actual divisibility flags agree with the symbolic identity flags away
from the accidental zeros of nonzero polynomials. -/
theorem polynomial_flags_agree {X I : Type*} {n : ℕ}
    (F : I → MvPolynomial (Fin n) ℚ) (value : X → Fin n → ℚ)
    (N : I → X → ℕ)
    (hzero : ∀ i x, N i x = 0 ↔ MvPolynomial.eval (value x) (F i) = 0)
    (x : X) (p : ℕ) (hgood : ∀ i, ¬(F i ≠ 0 ∧ p ∣ N i x)) :
    (fun i => arithmeticTestFlag (p ∣ N i x)) = (fun i => arithmeticTestFlag (F i = 0)) := by
  classical
  funext i
  by_cases hi : F i = 0
  · have hn : N i x = 0 := (hzero i x).mpr (by simp [hi])
    simp [hn, hi]
  · have hn : ¬p ∣ N i x := fun h => hgood i ⟨hi, h⟩
    simp [hi, hn]

private theorem weighted_prime_event_sum {X : Type*} [Fintype X]
    (P : Finset ℕ) (w : X → ℝ) (ν : ℕ → ℝ) (event : X → ℕ → Prop)
    [∀ x p, Decidable (event x p)] :
    (∑ xp : X × {p // p ∈ P}, (w xp.1 * ν xp.2) *
      if event xp.1 xp.2 then (1 : ℝ) else 0) =
    ∑ x, w x * ∑ p ∈ P, if event x p then ν p else 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_coe_sort P, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : event x p <;> simp [h]

private theorem polynomial_event_bound {A : Type*} [Fintype A] {n : ℕ}
    (value : A → ℚ) (hinj : Function.Injective value)
    (F : MvPolynomial (Fin n) ℚ)
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (α : ℝ) (hα : 0 ≤ α) (hmax : ∀ i a, μ i a ≤ α)
    (P : Finset ℕ) (ν : ℕ → ℝ) (hνmass : ∑ p ∈ P, ν p = 1)
    (N : (Fin n → A) → ℕ)
    (hzero : ∀ x, N x = 0 ↔ MvPolynomial.eval (fun j => value (x j)) F = 0)
    (β K : ℝ) (hβ : 0 ≤ β) (hK : 0 ≤ K) (hνmax : ∀ p ∈ P, ν p ≤ β)
    (hcard : ∀ x, N x ≠ 0 → ((P.filter fun p => p ∣ N x).card : ℝ) ≤ K) :
    (∑ xp : (Fin n → A) × {p // p ∈ P}, (productPrior μ xp.1 * ν xp.2) *
      if F ≠ 0 ∧ (xp.2 : ℕ) ∣ N xp.1 then (1 : ℝ) else 0) ≤
      (F.totalDegree : ℝ) * α + K * β := by
  classical
  rw [weighted_prime_event_sum P (productPrior μ) ν (fun x p => F ≠ 0 ∧ p ∣ N x)]
  by_cases hi : F = 0
  · simp only [hi, ne_eq, not_true_eq_false, false_and, ite_false,
      Finset.sum_const_zero, mul_zero]
    positivity
  · simp only [ne_eq, hi, not_false_eq_true, true_and]
    exact polynomial_prime_coincidence_le value hinj F hi μ hμ hmass
      α hα hmax P ν hνmass N hzero β K hβ hK hνmax hcard

/-- Signed comparison for any bounded amplitude depending on the coefficient
and minor flags, with the smooth and spectator variables left untouched. -/
theorem polynomial_symbolic_comparison_le {A I : Type*} [Fintype A] [Fintype I]
    {n : ℕ} (value : A → ℚ) (hinj : Function.Injective value)
    (F : I → MvPolynomial (Fin n) ℚ)
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (α : ℝ) (hα : 0 ≤ α) (hmax : ∀ i a, μ i a ≤ α)
    (P : Finset ℕ) (ν : ℕ → ℝ) (hν : ∀ p ∈ P, 0 ≤ ν p)
    (hνmass : ∑ p ∈ P, ν p = 1)
    (N : I → (Fin n → A) → ℕ)
    (hzero : ∀ i x, N i x = 0 ↔ MvPolynomial.eval (fun j => value (x j)) (F i) = 0)
    (β K : ℝ) (hβ : 0 ≤ β) (hK : 0 ≤ K) (hνmax : ∀ p ∈ P, ν p ≤ β)
    (hcard : ∀ i x, N i x ≠ 0 → ((P.filter fun p => p ∣ N i x).card : ℝ) ≤ K)
    (Ψ : (Fin n → A) → ℕ → (I → Bool) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hΨ : ∀ x p v, ‖Ψ x p v‖ ≤ B) :
    ‖∑ x, ∑ p ∈ P, ((productPrior μ x * ν p : ℝ) : ℂ) *
      (Ψ x p (fun i => arithmeticTestFlag (p ∣ N i x)) - Ψ x p (fun i => arithmeticTestFlag (F i = 0)))‖ ≤
      2 * B * ∑ i, (((F i).totalDegree : ℝ) * α + K * β) := by
  classical
  let X := (Fin n → A) × {p // p ∈ P}
  let w : X → ℝ := fun xp => productPrior μ xp.1 * ν xp.2
  let bad : I → X → Prop := fun i xp => F i ≠ 0 ∧ (xp.2 : ℕ) ∣ N i xp.1
  have hw : ∀ xp, 0 ≤ w xp := fun xp => mul_nonneg
    (productPrior_nonneg μ hμ xp.1) (hν xp.2 xp.2.property)
  have hprob (i : I) : (∑ xp : X, w xp * if bad i xp then 1 else 0) ≤
      ((F i).totalDegree : ℝ) * α + K * β :=
    polynomial_event_bound value hinj (F i) μ hμ hmass α hα hmax P ν hνmass
      (N i) (hzero i) β K hβ hK hνmax (hcard i)
  have heq (xp : X) (hgood : ∀ i, ¬bad i xp) :
      (fun i => arithmeticTestFlag ((xp.2 : ℕ) ∣ N i xp.1)) = (fun i => arithmeticTestFlag (F i = 0)) :=
    @polynomial_flags_agree (Fin n → A) I n F
      (fun (x : Fin n → A) j => value (x j)) N hzero xp.1 xp.2 hgood
  have hbnd (xp : X) (v : I → Bool) : ‖Ψ xp.1 xp.2 v‖ ≤ B := hΨ xp.1 xp.2 v
  have h := @weighted_flag_comparison_le X I inferInstance inferInstance w hw
    (fun xp i => arithmeticTestFlag ((xp.2 : ℕ) ∣ N i xp.1))
    (fun _ i => arithmeticTestFlag (F i = 0)) bad
    (fun _ _ => inferInstance) heq (fun xp => Ψ xp.1 xp.2) B hB hbnd
  have hbound := h.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ => hprob i) (by positivity : 0 ≤ 2 * B))
  let term : (Fin n → A) → ℕ → ℂ := fun x p =>
    ((productPrior μ x * ν p : ℝ) : ℂ) *
      (Ψ x p (fun i => arithmeticTestFlag (p ∣ N i x)) -
        Ψ x p (fun i => arithmeticTestFlag (F i = 0)))
  change ‖∑ xp : X, term xp.1 xp.2‖ ≤ _ at hbound
  have hsum : (∑ xp : X, term xp.1 xp.2) = ∑ x, ∑ p ∈ P, term x p := by
    change (∑ xp : (Fin n → A) × {p // p ∈ P}, term xp.1 xp.2) = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    exact (Finset.sum_subtype P (fun _ => Iff.rfl) (term x)).symm
  rw [hsum] at hbound
  exact hbound

end Ostmann

end OAI
