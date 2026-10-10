import OAI.NumberTheory.Ostmann.Arithmetic.PolynomialFlagReplacementWeighted
import OAI.NumberTheory.Ostmann.Arithmetic.ProductExpectationFinite

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PolynomialFlagReplacementFinite
open scoped BigOperators
open MvPolynomial

def divisibilityIndicator {ι : Type*} (P : MvPolynomial ι ℤ) (x : ι → ℤ) (b : ℕ) : ℝ :=
  if (b:ℤ) ∣ eval x P then 1 else 0

def flagError {ι : Type*} (P : MvPolynomial ι ℤ) (x : ι → ℤ) (b : ℕ) : ℝ := by
  classical
  exact |divisibilityIndicator P x b-if P=0 then 1 else 0|

@[simp] theorem zero_polynomial_flag {ι : Type*} (x : ι → ℤ) (b : ℕ) :
    divisibilityIndicator (0 : MvPolynomial ι ℤ) x b=1 := by
  simp [divisibilityIndicator]

@[simp] theorem zero_polynomial_error {ι : Type*} (x : ι → ℤ) (b : ℕ) :
    flagError (0 : MvPolynomial ι ℤ) x b=0 := by simp [flagError]

theorem flagError_nonneg {ι : Type*} (P : MvPolynomial ι ℤ) (x : ι → ℤ) (b : ℕ) :
    0 ≤ flagError P x b := abs_nonneg _

theorem totalDegree_rename_equiv {ι κ : Type*} (e : ι ≃ κ) (P : MvPolynomial ι ℤ) :
    (rename e P).totalDegree=P.totalDegree := totalDegree_renameEquiv e P

theorem rename_ne_zero {ι κ : Type*} (e : ι ≃ κ) {P : MvPolynomial ι ℤ} (hP : P≠0) :
    rename e P≠0 := by
  exact fun h => hP ((rename_eq_zero_iff_of_injective P e.injective).mp h)

@[simp] theorem eval_rename_equiv {ι κ : Type*} (e : ι ≃ κ) (P : MvPolynomial ι ℤ)
    (x : κ → ℤ) : eval x (rename e P)=eval (x ∘ e) P := eval_rename e x P

@[simp] theorem divisibilityIndicator_rename_equiv {ι κ : Type*} (e : ι ≃ κ)
    (P : MvPolynomial ι ℤ) (x : κ → ℤ) (b : ℕ) :
    divisibilityIndicator (rename e P) x b=divisibilityIndicator P (x ∘ e) b := by
  simp only [divisibilityIndicator,eval_rename_equiv]

@[simp] theorem flagError_rename_equiv {ι κ : Type*} (e : ι ≃ κ)
    (P : MvPolynomial ι ℤ) (x : κ → ℤ) (b : ℕ) :
    flagError (rename e P) x b=flagError P (x ∘ e) b := by
  classical
  by_cases hP : P=0
  · subst P
    simp only [map_zero,zero_polynomial_error]
  · simp only [flagError,divisibilityIndicator_rename_equiv,hP,rename_ne_zero e hP,ite_false]

theorem fin_flagError_eq {n : ℕ} (P : MvPolynomial (Fin n) ℤ) (x : Fin n → ℤ) (b : ℕ) :
    PolynomialFlagReplacement.flagError P x b=flagError P x b := by
  classical
  by_cases hP : P=0
  · subst P
    rw [PolynomialFlagReplacement.zero_polynomial_error,zero_polynomial_error]
  · by_cases hd : (b:ℤ) ∣ eval x P
    · simp only [PolynomialFlagReplacement.flagError,flagError,
        PolynomialFlagReplacement.divisibilityIndicator,divisibilityIndicator,hP,hd,ite_true,ite_false]
    · simp only [PolynomialFlagReplacement.flagError,flagError,
        PolynomialFlagReplacement.divisibilityIndicator,divisibilityIndicator,hP,hd,ite_false]

theorem product_sum_reindex {ι κ K : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (S : ι → Finset K) (μ : ι → K → ℝ) (f : (ι → K) → ℝ) :
    (∑ x ∈ Fintype.piFinset (fun j => S (e.symm j)),
      (∏j,μ (e.symm j) (x j))*f (x ∘ e)) =
    ∑ x ∈ Fintype.piFinset S,(∏i,μ i (x i))*f x := by
  classical
  apply Finset.sum_bij (fun x _ => x ∘ e)
  · intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    simpa only [Function.comp_apply,e.symm_apply_apply] using Fintype.mem_piFinset.mp hx (e i)
  · intro x hx y hy hxy
    funext j
    have hh := congrFun hxy (e.symm j)
    simpa only [Function.comp_apply,e.apply_symm_apply] using hh
  · intro y hy
    refine ⟨y ∘ e.symm,?_,?_⟩
    · exact Fintype.mem_piFinset.mpr (fun j => Fintype.mem_piFinset.mp hy (e.symm j))
    · funext i
      simp only [Function.comp_apply,e.symm_apply_apply]
  · intro x hx
    congr 1
    exact Fintype.prod_equiv e.symm _ _ (fun j => by simp only [Function.comp_apply,e.apply_symm_apply])

theorem expectation_reindex_eq_product_sum {ι K : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : ι → Finset K) (μ : ι → K → ℝ) (f : (ι → K) → ℝ) :
    ProductExpectation.expectation (fun j => S (e.symm j)) (fun j => μ (e.symm j))
      (fun x => f (x ∘ e)) = ∑ x ∈ Fintype.piFinset S,(∏i,μ i (x i))*f x := by
  rw [ProductExpectation.eq_product_sum]
  exact product_sum_reindex e S μ f

end Ostmann.Arithmetic.PolynomialFlagReplacementFinite

end

end OAI
