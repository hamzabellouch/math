import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import OAI.NumberTheory.Ostmann.Preliminaries.TransferCauchy

namespace OAI

/-! # Symmetrization under the identical original bulk priors -/

namespace Ostmann

open scoped BigOperators Classical

def permuteBulk {I A : Type*} (e : Equiv.Perm I) (x : I → A) : I → A :=
  x ∘ e.symm

def bulkArrayEquiv {I A : Type*} (e : Equiv.Perm I) : (I → A) ≃ (I → A) where
  toFun := permuteBulk e
  invFun := permuteBulk e.symm
  left_inv x := by funext i; simp [permuteBulk]
  right_inv x := by funext i; simp [permuteBulk]

noncomputable def identicalBulkPrior {I A : Type*} [Fintype I]
    (μ : A → ℝ) (x : I → A) : ℝ := ∏ i, μ (x i)

theorem identicalBulkPrior_permute {I A : Type*} [Fintype I]
    (μ : A → ℝ) (e : Equiv.Perm I) (x : I → A) :
    identicalBulkPrior μ (permuteBulk e x) = identicalBulkPrior μ x := by
  exact e.symm.prod_comp (fun i => μ (x i))

theorem bulk_value_product_permute {I A M : Type*} [Fintype I] [CommMonoid M]
    (h : A → M) (e : Equiv.Perm I) (x : I → A) :
    (∏ i, h (permuteBulk e x i)) = ∏ i, h (x i) :=
  e.symm.prod_comp (fun i => h (x i))

noncomputable def bulkSymmetrize {I A : Type*} [Fintype I] [DecidableEq I]
    (F : (I → A) → ℂ) (x : I → A) : ℂ :=
  (Fintype.card (Equiv.Perm I) : ℂ)⁻¹ * ∑ e : Equiv.Perm I, F (permuteBulk e x)

/-- The statistic is unchanged even if all bins and history restrictions
are carried by F and have no permutation invariance. -/
theorem bulkSymmetrize_statistic {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (μ : A → ℝ) (G F : (I → A) → ℂ)
    (hG : ∀ e x, G (permuteBulk e x) = G x) :
    (∑ x : I → A, (identicalBulkPrior μ x : ℂ) * G x * bulkSymmetrize F x) =
      ∑ x : I → A, (identicalBulkPrior μ x : ℂ) * G x * F x := by
  have hc : (Fintype.card (Equiv.Perm I) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hs (e : Equiv.Perm I) :
      (∑ x : I → A, (identicalBulkPrior μ x : ℂ) * G x * F (permuteBulk e x)) =
        ∑ x : I → A, (identicalBulkPrior μ x : ℂ) * G x * F x := by
    have h := (bulkArrayEquiv (A := A) e).sum_comp
      (fun x => (identicalBulkPrior μ x : ℂ) * G x * F x)
    simpa only [bulkArrayEquiv, Equiv.coe_fn_mk, identicalBulkPrior_permute, hG] using h
  unfold bulkSymmetrize
  simp only [Finset.mul_sum]
  simp_rw [show ∀ (x : I → A) (e : Equiv.Perm I),
    (identicalBulkPrior μ x : ℂ) * G x *
      ((Fintype.card (Equiv.Perm I) : ℂ)⁻¹ * F (permuteBulk e x)) =
    (Fintype.card (Equiv.Perm I) : ℂ)⁻¹ *
      ((identicalBulkPrior μ x : ℂ) * G x * F (permuteBulk e x)) by intros; ring]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Weighted Cauchy--Schwarz at the final symmetrized statistic. -/
theorem bulkSymmetrize_cauchy {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (G F : (I → A) → ℂ) :
    ‖∑ x : I → A, (identicalBulkPrior μ x : ℂ) * G x * bulkSymmetrize F x‖ ^ 2 ≤
      (∑ x : I → A, identicalBulkPrior μ x * ‖G x‖ ^ 2) *
        ∑ x : I → A, identicalBulkPrior μ x * ‖bulkSymmetrize F x‖ ^ 2 := by
  have hp (x : I → A) : 0 ≤ identicalBulkPrior μ x :=
    Finset.prod_nonneg (fun i _ => hμ (x i))
  have hs (x : I → A) : Real.sqrt (identicalBulkPrior μ x) ^ 2 =
      identicalBulkPrior μ x := Real.sq_sqrt (hp x)
  have h := complex_pairing_sq_le
    (fun x : I → A => (Real.sqrt (identicalBulkPrior μ x) : ℂ) * G x)
    (fun x : I → A => (Real.sqrt (identicalBulkPrior μ x) : ℂ) * bulkSymmetrize F x)
  have hprod (x : I → A) :
      ((Real.sqrt (identicalBulkPrior μ x) : ℂ) * G x) *
        ((Real.sqrt (identicalBulkPrior μ x) : ℂ) * bulkSymmetrize F x) =
      (identicalBulkPrior μ x : ℂ) * G x * bulkSymmetrize F x := by
    have hcast := congrArg (fun t : ℝ => (t : ℂ)) (hs x)
    push_cast at hcast
    calc
      _ = ((Real.sqrt (identicalBulkPrior μ x) : ℂ) ^ 2) * G x * bulkSymmetrize F x := by ring
      _ = _ := by rw [hcast]
  simpa only [hprod, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hs] using h

end Ostmann

end OAI
