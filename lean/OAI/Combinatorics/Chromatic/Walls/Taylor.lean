import Mathlib

namespace OAI

section
namespace ElementaryPositivity.CommonTranslation

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem coefficients_mem {N : ℕ} (U : Submodule ℚ V) (v : Fin N → V)
    (h : ∀ t : ℚ, ∑ n : Fin N, t^(n:ℕ) • v n ∈ U) (n : Fin N) : v n ∈ U := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U (v n)).mp
  intro φ hφ
  let p : Polynomial ℚ := ∑ k : Fin N, Polynomial.monomial (k:ℕ) (φ (v k))
  have hp : p = 0 := by
    apply Polynomial.zero_of_eval_zero
    intro t
    have hz : φ (∑ k : Fin N, t^(k:ℕ) • v k) = 0 := ((Submodule.mem_dualAnnihilator φ).mp hφ) _ (h t)
    simpa [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      map_sum, map_smul, mul_comm] using hz
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff (n:ℕ)) hp
  simpa [p, Polynomial.coeff_sum, Polynomial.coeff_monomial,
    ← Fin.ext_iff] using hc

variable {A : Type*} [CommRing A] [Algebra ℚ A]

theorem polynomial_coeff_mem (U : Submodule ℚ A) (p : Polynomial A)
    (h : ∀ t : ℚ, p.eval (algebraMap ℚ A t) ∈ U) (n : ℕ) : p.coeff n ∈ U := by
  by_cases hn : n < p.natDegree+1
  · apply coefficients_mem U (fun k : Fin (p.natDegree+1) => p.coeff k.val) ?_ ⟨n,hn⟩
    intro t
    convert h t using 1
    rw [Polynomial.eval_eq_sum_range]
    simp only [Algebra.smul_def, map_pow]
    rw [Fin.sum_univ_eq_sum_range (fun i => (algebraMap ℚ A t)^i * p.coeff i)]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact U.zero_mem

section Polynomials
open MvPolynomial
variable {α β : Type*}

noncomputable def taylor : MvPolynomial α ℚ →ₐ[ℚ] Polynomial (MvPolynomial α ℚ) :=
  aeval fun i => Polynomial.C (X i) + Polynomial.X

@[simp] lemma taylor_X (i : α) :
    taylor (X i) = Polynomial.C (X i) + Polynomial.X := by simp [taylor]

@[simp] lemma taylor_C (r : ℚ) :
    taylor (C r : MvPolynomial α ℚ) = Polynomial.C (C r) := by
  simp [taylor, Polynomial.algebraMap_apply]

lemma taylor_eval (p : MvPolynomial α ℚ) (t : ℚ) :
    (taylor p).eval (C t) = aeval (fun i => X i + C t) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]

@[simp] lemma taylor_coeff_zero (p : MvPolynomial α ℚ) : (taylor p).coeff 0 = p := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have h := taylor_eval p 0
  simpa [show (aeval fun i : α => X i + C (0:ℚ)) = AlgHom.id ℚ _ by ext; simp] using h

noncomputable def D : Derivation ℚ (MvPolynomial α ℚ) (MvPolynomial α ℚ) :=
  mkDerivation ℚ fun _ => 1

@[simp] lemma D_X (i : α) : D (X i) = 1 := mkDerivation_X ℚ _ i
@[simp] lemma D_C (r : ℚ) : D (C r : MvPolynomial α ℚ) = 0 := derivation_C _ _
lemma D_mul (p q : MvPolynomial α ℚ) : D (p*q) = D p*q + p*D q := by
  simp [smul_eq_mul, mul_comm, add_comm]

lemma D_eq_sum [Fintype α] : D (α := α) = ∑ i : α, pderiv i := by
  classical
  apply MvPolynomial.derivation_ext
  intro i
  rw [show (∑ j : α, pderiv j) (X i) = ∑ j : α, pderiv j (X i) from by
    simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using
      congrFun (map_sum Derivation.coeFnAddMonoidHom (fun j : α => pderiv j) Finset.univ) (X i)]
  simp [pderiv_X, Pi.single_apply]

lemma taylor_derivative (p : MvPolynomial α ℚ) :
    Polynomial.derivative (taylor p) = taylor (D p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.derivative_mul, taylor_X,
      Polynomial.derivative_C, Polynomial.derivative_X, zero_add, mul_one, hp,
      D_mul, D_X, map_add]

@[simp] lemma taylor_coeff_one (p : MvPolynomial α ℚ) : (taylor p).coeff 1 = D p := by
  have h := congrArg (fun q : Polynomial (MvPolynomial α ℚ) => q.coeff 0) (taylor_derivative p)
  simpa [Polynomial.coeff_derivative] using h

lemma D_rename (f : α → β) (p : MvPolynomial α ℚ) :
    D (rename f p) = rename f (D p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]

theorem D_mem_of_translation_mem (U : Submodule ℚ (MvPolynomial α ℚ))
    (p : MvPolynomial α ℚ)
    (h : ∀ t : ℚ, aeval (fun i => X i + C t) p ∈ U) : D p ∈ U := by
  have hc := polynomial_coeff_mem U (taylor p) (fun t => by simpa [taylor_eval] using h t) 1
  simpa using hc

lemma taylor_iterate_D (n : ℕ) (p : MvPolynomial α ℚ) :
    taylor ((D.toLinearMap ^ n) p) = (Polynomial.derivative^[n]) (taylor p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    change taylor (D ((D.toLinearMap^n) p)) = _
    rw [← taylor_derivative, ih, Function.iterate_succ_apply']

theorem locally_nilpotent_D (p : MvPolynomial α ℚ) :
    (D.toLinearMap ^ ((taylor p).natDegree+1)) p = 0 := by
  have h := taylor_iterate_D ((taylor p).natDegree+1) p
  rw [Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _)] at h
  have h0 := congrArg (fun q : Polynomial (MvPolynomial α ℚ) => q.coeff 0) h
  simpa using h0

end Polynomials

end ElementaryPositivity.CommonTranslation

end

end OAI
