import Mathlib

namespace OAI

/-! Box Monomials. -/

noncomputable section
open scoped BigOperators
namespace BoxMonomials
open MvPolynomial

abbrev Box (m t : ℕ) := Fin m → Fin (t+1)

def exponent {m t : ℕ} (e : Box m t) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (e i).val)

@[simp] lemma exponent_apply {m t : ℕ} (e : Box m t) (i : Fin m) :
    exponent e i=(e i).val := rfl

lemma exponent_injective (m t : ℕ) : Function.Injective (@exponent m t) := by
  intro e f h
  funext i
  apply Fin.ext
  exact congrArg (fun s : Fin m →₀ ℕ => s i) h

def affine {m t : ℕ} (e : Box m t) : MvPolynomial (Fin m) ℂ :=
  monomial (exponent e) 1

lemma affine_independent (m t : ℕ) : LinearIndependent ℂ (@affine m t) :=
  (basisMonomials (Fin m) ℂ).linearIndependent.comp _ (exponent_injective m t)

lemma eval_affine {m t : ℕ} (e : Box m t) (v : Fin m → ℂ) :
    eval v (affine e)=∏i,v i^(e i).val := by
  classical
  simp only [affine,eval_monomial,one_mul]
  exact Finsupp.prod_fintype _ _ (by simp)

lemma degree_le {m t : ℕ} (e : Box m t) : (∑i,(e i).val) ≤ m*t := by
  calc
    (∑i,(e i).val) ≤ ∑i : Fin m,t :=
      Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (e i).isLt)
    _ = m*t := by simp

def homogeneous {σ : Type*} {m t : ℕ} (j : σ) (v : Fin m → σ) (e : Box m t) :
    homogeneousSubmodule σ ℂ (m*t) :=
  ⟨X j^(m*t-∑i,(e i).val)*∏i,X (v i)^(e i).val,by
    apply (mem_homogeneousSubmodule _ _).mpr
    have h₁ := isHomogeneous_X_pow (R := ℂ) j (m*t-∑i,(e i).val)
    have h₂ := IsHomogeneous.prod Finset.univ (fun i => (X (v i) : MvPolynomial σ ℂ)^(e i).val)
      (fun i => (e i).val) (fun i _ => isHomogeneous_X_pow _ _)
    simpa only [Nat.sub_add_cancel (degree_le e)] using h₁.mul h₂⟩

lemma eval_homogeneous {σ : Type*} {m t : ℕ} (j : σ) (v : Fin m → σ)
    (e : Box m t) (x : σ → ℂ) (hj : x j≠0) :
    eval x (homogeneous j v e).val = (x j)^(m*t)*eval (fun i => x (v i)/x j) (affine e) := by
  classical
  simp only [homogeneous,eval_mul,map_pow,eval_X,map_prod,eval_affine,div_pow,
    Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]
  rw [pow_sub₀ _ hj (degree_le e)]
  field_simp

end BoxMonomials

end

end OAI
