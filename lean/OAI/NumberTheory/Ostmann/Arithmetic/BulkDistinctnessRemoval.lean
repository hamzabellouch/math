import Mathlib.Analysis.Complex.Basic
import OAI.NumberTheory.Ostmann.Tree.IndependentCoordinate
import OAI.NumberTheory.Ostmann.Construction.PrimePriorDecay
import OAI.NumberTheory.Ostmann.Construction.FiniteEnumeration

namespace OAI

/-! # Removing bulk-prime collisions under the original independent priors -/

namespace Ostmann
open scoped Classical BigOperators

theorem productPrior_pair_collision_le {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1) (α : ℝ) (hmax : ∀ i a, μ i a ≤ α)
    (i j : Fin n) (hij : i ≠ j) :
    (∑ x : Fin n → A, productPrior μ x * if x i = x j then (1 : ℝ) else 0) ≤ α := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hij.symm
    rw [sum_productPrior_insertNth μ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    have hs (x : Fin n → A) :
        (∑ a, μ i a * if a = x t then (1 : ℝ) else 0) = μ i (x t) := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp_rw [hs]
    calc
      _ ≤ ∑ x : Fin n → A, productPrior (fun j => μ (i.succAbove j)) x * α :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hmax i (x t))
          (productPrior_nonneg _ (fun j a => hμ (i.succAbove j) a) x)
      _ = α := by rw [← Finset.sum_mul, productPrior_mass _ (fun j => hmass (i.succAbove j)), one_mul]

/-- Ordered pairs suffice; the harmless square count avoids selecting an
ordering of the actual bulk positions. -/
theorem productPrior_noninjective_le {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1) (α : ℝ) (hα : 0 ≤ α)
    (hmax : ∀ i a, μ i a ≤ α) :
    (∑ x : Fin n → A, productPrior μ x * if Function.Injective x then (0 : ℝ) else 1) ≤
      (n : ℝ) ^ 2 * α := by
  let bad := fun (x : Fin n → A) (ij : Fin n × Fin n) =>
    if ij.1 ≠ ij.2 ∧ x ij.1 = x ij.2 then (1 : ℝ) else 0
  have hpoint (x : Fin n → A) :
      (if Function.Injective x then (0 : ℝ) else 1) ≤ ∑ ij, bad x ij := by
    by_cases hx : Function.Injective x
    · rw [ite_eq_left hx]
      exact Finset.sum_nonneg fun ij _ => by dsimp [bad]; positivity
    · rw [ite_eq_right hx]
      have hw : ∃ i j, i ≠ j ∧ x i = x j := by
        by_contra! h
        exact hx (fun i j hij => by by_contra hne; exact h i j hne hij)
      obtain ⟨i, j, hij, heq⟩ := hw
      calc
        (1 : ℝ) = bad x (i, j) := by simp [bad, hij, heq]
        _ ≤ ∑ ij, bad x ij := Finset.single_le_sum
          (fun ij _ => by dsimp [bad]; positivity) (Finset.mem_univ _)
  calc
    _ ≤ ∑ x : Fin n → A, productPrior μ x * ∑ ij, bad x ij :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x)
        (productPrior_nonneg μ hμ x)
    _ = ∑ ij, ∑ x : Fin n → A, productPrior μ x * bad x ij := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ _ij : Fin n × Fin n, α := by
      apply Finset.sum_le_sum
      intro ij _
      by_cases hij : ij.1 = ij.2
      · simpa [bad, hij] using hα
      · simpa [bad, hij] using
          productPrior_pair_collision_le μ hμ hmass α hmax ij.1 ij.2 hij
    _ = (n : ℝ) ^ 2 * α := by simp [pow_two, mul_assoc]

/-- Removing the distinctness gate costs its original collision probability,
even when the complex integrand includes all the retained arithmetic factors. -/
theorem bulk_distinctness_removal {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1) (α : ℝ) (hα : 0 ≤ α)
    (hmax : ∀ i a, μ i a ≤ α) (F : (Fin n → A) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ x : Fin n → A, (productPrior μ x : ℂ) *
        (if Function.Injective x then F x else 0)) -
      ∑ x : Fin n → A, (productPrior μ x : ℂ) * F x‖ ≤ B * (n : ℝ) ^ 2 * α := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x : Fin n → A, B * (productPrior μ x *
        if Function.Injective x then (0 : ℝ) else 1) := by
      apply norm_sum_le_of_le
      intro x _
      by_cases hx : Function.Injective x
      · simp [hx]
      · simp only [hx, ite_false, mul_zero, zero_sub, norm_neg, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg (productPrior_nonneg μ hμ x), mul_one]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hF x)
          (productPrior_nonneg μ hμ x)
    _ = B * ∑ x : Fin n → A, productPrior μ x *
        if Function.Injective x then (0 : ℝ) else 1 := (Finset.mul_sum _ _ _).symm
    _ ≤ B * ((n : ℝ) ^ 2 * α) := mul_le_mul_of_nonneg_left
      (productPrior_noninjective_le μ hμ hmass α hα hmax) hB
    _ = _ := by ring

/-- The collision estimate for the literal bulk harmonic cells. The ambient
prime set may also contain all nonbulk roles; the lower endpoint is needed
only on the support of each bulk prior. -/
theorem original_bulk_distinctness_removal {n : ℕ}
    (P : Finset ℕ) (Q : Fin n → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (H T : ℝ) (hmass : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp H)
    (hlow : ∀ i p, p ∈ Q i → Real.exp T ≤ (p : ℝ))
    (F : (Fin n → P) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ x : Fin n → P, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
        (if Function.Injective x then F x else 0)) -
      ∑ x : Fin n → P, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) * F x‖ ≤
      B * (n : ℝ) ^ 2 * Real.exp (H - T) := by
  have hmax (i : Fin n) (p : P) : primeSubsetPrior P (Q i) p ≤ Real.exp (H - T) := by
    by_cases hp : (p : ℕ) ∈ Q i
    · exact primeSubsetPrior_le_exp P (Q i) p H T (hmass i) (hlow i p hp)
    · simpa only [primeSubsetPrior, hp, ite_false] using Real.exp_nonneg (H - T)
  have h := bulk_distinctness_removal (fun i => primeSubsetPrior P (Q i))
    (fun i p => primeSubsetPrior_nonneg P (Q i) p)
    (fun i => primeSubsetPrior_mass P (Q i) (hQP i) (hQ i))
    (Real.exp (H - T)) (Real.exp_nonneg _) hmax F B hB hF
  simp only [finite_univ_canonical] at h ⊢
  convert h using 1
  congr 2
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  split_ifs <;> rfl

end Ostmann

end OAI
