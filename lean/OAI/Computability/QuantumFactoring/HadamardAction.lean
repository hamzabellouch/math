import Mathlib
import OAI.Computability.QuantumFactoring.SuperpositionGates
import OAI.Computability.QuantumFactoring.EncodedStates

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma hadamardAt_symmetric {q : ℕ} (j : Fin q) (x y : Basis q) :
    (hadamardAt j).matrix x y = (hadamardAt j).matrix y x := by
  rw [hadamardAt_matrix, hadamardAt_matrix]
  have h : (∀ i, i ≠ j → x i = y i) ↔ (∀ i, i ≠ j → y i = x i) := by
    constructor <;> intro h i hi <;> exact (h i hi).symm
  simp only [h, Bool.and_comm]

lemma hadamardAt_apply_direct_sum {q : ℕ} (j : Fin q) (ψ : State q) (x : Basis q) :
    (hadamardAt j).matrix.mulVec ψ x =
      (ψ (Function.update x j false) +
        (if x j then (-1:ℂ) else 1)*ψ (Function.update x j true)) / (Real.sqrt 2:ℂ) := by
  classical
  have h (y : Basis q) := congrFun (hadamardAt_basis j x) y
  rw [matrix_basisVector] at h
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisVector] at h
  change (∑ y, (hadamardAt j).matrix x y * ψ y) = _
  simp_rw [hadamardAt_symmetric j x, h]
  simp only [mul_add, add_mul, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  cases x j <;> simp <;> ring

noncomputable def localHadamard {A : Type*} [Fintype A] {b : ℕ} (j : Fin b) :
    Matrix (Basis b × A) (Basis b × A) ℂ := by
  classical
  exact fun v u => if v.2=u.2 then (hadamardAt j).matrix v.1 u.1 else 0

lemma localHadamard_apply {A : Type*} [Fintype A] {b : ℕ} (j : Fin b)
    (ψ : Basis b × A → ℂ) (v : Basis b × A) :
    (localHadamard (A:=A) j).mulVec ψ v =
      (ψ (Function.update v.1 j false,v.2) +
        (if v.1 j then (-1:ℂ) else 1)*ψ (Function.update v.1 j true,v.2)) /
          (Real.sqrt 2:ℂ) := by
  classical
  change (∑ u : Basis b × A, (if v.2=u.2 then (hadamardAt j).matrix v.1 u.1 else 0) * ψ u) = _
  simp only [Fintype.sum_prod_type, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simpa only [Matrix.mulVec, dotProduct, ite_mul] using
    hadamardAt_apply_direct_sum j (fun d => ψ (d,v.2)) v.1

lemma localHadamard_basis {A : Type*} [Fintype A] [DecidableEq A] {b : ℕ} (j : Fin b)
    (u : Basis b × A) :
    (fun v => localHadamard (A:=A) j v u) =
      (Real.sqrt 2:ℂ)⁻¹ • (basisVector (Function.update u.1 j false,u.2) +
        (if u.1 j then (-1:ℂ) else 1) • basisVector (Function.update u.1 j true,u.2)) := by
  classical
  funext v
  have h := congrFun (hadamardAt_basis j u.1) v.1
  rw [matrix_basisVector] at h
  simp only [localHadamard, Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisVector,
    Prod.ext_iff] at h ⊢
  by_cases hv : v.2=u.2
  · simp only [hv, and_true, ite_true]
    exact h
  · simp [hv]

/-- Logical H on data is physically H on the corresponding encoded wire,
provided the embedding preserves that bit and its two updates. -/
lemma encoded_hadamard {A : Type*} [Fintype A] [DecidableEq A] {b q : ℕ}
    (e : Basis b × A → Basis q) (j : Fin b) (t : Fin q)
    (hbit : ∀ u, e u t = u.1 j)
    (hupdate : ∀ u c, Function.update (e u) t c = e (Function.update u.1 j c,u.2))
    (ψ : Basis b × A → ℂ) :
    (hadamardAt t).matrix.mulVec (encodeState e ψ) =
      encodeState e ((localHadamard (A:=A) j).mulVec ψ) := by
  apply matrix_encodeState
  intro u
  rw [hadamardAt_basis, localHadamard_basis, hbit, hupdate, hupdate,
    encodeState_smul, encodeState_add, encodeState_smul, encodeState_basis, encodeState_basis]

end ExactQuantumFactoring


end

end OAI
