import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fintype.BigOperators

namespace OAI

/-!
# Guarded homogenization of affine incidence equations
-/

section

noncomputable section

namespace Nagata.W27

open scoped BigOperators
open MvPolynomial

variable {r : ℕ} {R : Type*} [CommRing R]

/-- Affine degree in one point-coordinate block. -/
def blockOrder (a : (Fin r × Fin 2) →₀ ℕ) (i : Fin r) : ℕ :=
  a (i, 0) + a (i, 1)

/-- A separate degree bound for each point-coordinate block. -/
def blockDegreeBound (f : MvPolynomial (Fin r × Fin 2) R) (i : Fin r) : ℕ :=
  f.support.sup (fun a => blockOrder a i)

theorem blockOrder_le_bound (f : MvPolynomial (Fin r × Fin 2) R)
    (a : (Fin r × Fin 2) →₀ ℕ) (ha : a ∈ f.support) (i : Fin r) :
    blockOrder a i ≤ blockDegreeBound f i := by
  exact Finset.le_sup (f := fun a => blockOrder a i) ha

/-- Insert the distinguished projective-coordinate exponent. The extra one
is the guard: every term vanishes outside the chosen product affine chart. -/
def guardedExponent (c : Fin r → Fin 3) (D : Fin r → ℕ)
    (a : (Fin r × Fin 2) →₀ ℕ) : (Fin r × Fin 3) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ij : Fin r × Fin 3 =>
    Fin.insertNth (α := fun _ : Fin 3 => ℕ) (c ij.1)
      (D ij.1 - blockOrder a ij.1 + 1)
      (fun j => a (ij.1, j)) ij.2

@[simp] theorem guardedExponent_same (c : Fin r → Fin 3) (D : Fin r → ℕ)
    (a : (Fin r × Fin 2) →₀ ℕ) (i : Fin r) :
    guardedExponent c D a (i, c i) = D i - blockOrder a i + 1 := by
  simp [guardedExponent]

@[simp] theorem guardedExponent_other (c : Fin r → Fin 3) (D : Fin r → ℕ)
    (a : (Fin r × Fin 2) →₀ ℕ) (i : Fin r) (j : Fin 2) :
    guardedExponent c D a (i, (c i).succAbove j) = a (i, j) := by
  simp [guardedExponent]

theorem guardedExponent_block_sum (c : Fin r → Fin 3) (D : Fin r → ℕ)
    (a : (Fin r × Fin 2) →₀ ℕ) (i : Fin r) (ha : blockOrder a i ≤ D i) :
    (∑ j : Fin 3, guardedExponent c D a (i, j)) = D i + 1 := by
  rw [Fin.sum_univ_succAbove _ (c i)]
  simp only [guardedExponent_same, guardedExponent_other, Fin.sum_univ_two]
  unfold blockOrder at *
  omega

/-- Guarded block homogenization of an arbitrary affine polynomial. -/
def guardedHomogenize (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R) : MvPolynomial (Fin r × Fin 3) R :=
  ∑ a ∈ f.support, monomial (guardedExponent c (blockDegreeBound f) a) (f.coeff a)

/-- Each actual support monomial has the prescribed degree in every block. -/
theorem guardedHomogenize_homogeneous (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R)
    (b : (Fin r × Fin 3) →₀ ℕ) (hb : b ∈ (guardedHomogenize c f).support)
    (i : Fin r) : (∑ j : Fin 3, b (i, j)) = blockDegreeBound f i + 1 := by
  classical
  have hcoeff : (guardedHomogenize c f).coeff b ≠ 0 := mem_support_iff.mp hb
  simp only [guardedHomogenize, coeff_sum] at hcoeff
  obtain ⟨a, ha, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
  have heq : guardedExponent c (blockDegreeBound f) a = b := by
    by_contra hne
    exact hterm (by simp [coeff_monomial, hne])
  rw [← heq]
  exact guardedExponent_block_sum c _ a i (blockOrder_le_bound f a ha i)

/-- A zero distinguished coordinate kills every guarded term. -/
theorem eval_guardedHomogenize_zero (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R) (v : Fin r × Fin 3 → R)
    (i : Fin r) (hi : v (i, c i) = 0) :
    eval v (guardedHomogenize c f) = 0 := by
  classical
  simp only [guardedHomogenize, map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ (i, c i))
  rw [guardedExponent_same, hi]
  exact zero_pow (by omega)

/-- On normalized homogeneous representatives the homogenized polynomial
evaluates to the original affine polynomial. -/
theorem eval_guardedHomogenize_normalized (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R) (v : Fin r × Fin 3 → R)
    (hv : ∀ i, v (i, c i) = 1) :
    eval v (guardedHomogenize c f) =
      eval (fun ij => v (ij.1, (c ij.1).succAbove ij.2)) f := by
  classical
  rw [eval_eq' _ f]
  simp only [guardedHomogenize, map_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Fin.prod_univ_succAbove _ (c i)]
  simp only [guardedExponent_same, guardedExponent_other, hv, one_pow, one_mul]

/-- Scaling each homogeneous coordinate block scales the polynomial by its
actual block degree. -/
theorem eval_guardedHomogenize_scale (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R)
    (a : Fin r → R) (v : Fin r × Fin 3 → R) :
    eval (fun ij => a ij.1 * v ij) (guardedHomogenize c f) =
      (∏ i, a i ^ (blockDegreeBound f i + 1)) * eval v (guardedHomogenize c f) := by
  classical
  simp only [eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hprod : (∏ ij : Fin r × Fin 3, a ij.1 ^ b ij) =
      ∏ i, a i ^ (blockDegreeBound f i + 1) := by
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i hi
    change (∏ j : Fin 3, a i ^ b (i, j)) = a i ^ (blockDegreeBound f i + 1)
    rw [Finset.prod_pow_eq_pow_sum, guardedHomogenize_homogeneous c f b hb i]
  rw [hprod]
  ac_rfl

/-- For arbitrary nonzero chart coordinates the denominator-clearing factor
is explicit and nonzero. -/
theorem eval_guardedHomogenize_chart {K : Type*} [Field K]
    (c : Fin r → Fin 3) (f : MvPolynomial (Fin r × Fin 2) K)
    (v : Fin r × Fin 3 → K) (hv : ∀ i, v (i, c i) ≠ 0) :
    eval v (guardedHomogenize c f) =
      (∏ i, v (i, c i) ^ (blockDegreeBound f i + 1)) *
        eval (fun ij => v (ij.1, (c ij.1).succAbove ij.2) / v (ij.1, c ij.1)) f := by
  have h := eval_guardedHomogenize_scale c f
    (fun i => v (i, c i)) (fun ij => v ij / v (ij.1, c ij.1))
  have heq : (fun ij : Fin r × Fin 3 =>
      v (ij.1, c ij.1) * (v ij / v (ij.1, c ij.1))) = v := by
    funext ij
    exact mul_div_cancel₀ _ (hv ij.1)
  rw [heq] at h
  rw [eval_guardedHomogenize_normalized c f
    (fun ij => v ij / v (ij.1, c ij.1)) (fun i => div_self (hv i))] at h
  exact h

theorem eval_guardedHomogenize_eq_zero_iff {K : Type*} [Field K]
    (c : Fin r → Fin 3) (f : MvPolynomial (Fin r × Fin 2) K)
    (v : Fin r × Fin 3 → K) (hv : ∀ i, v (i, c i) ≠ 0) :
    eval v (guardedHomogenize c f) = 0 ↔
      eval (fun ij => v (ij.1, (c ij.1).succAbove ij.2) / v (ij.1, c ij.1)) f = 0 := by
  rw [eval_guardedHomogenize_chart c f v hv]
  have hfactor : (∏ i, v (i, c i) ^ (blockDegreeBound f i + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hv i)
  exact mul_eq_zero.trans (or_iff_right hfactor)

end Nagata.W27

end
end

end OAI
