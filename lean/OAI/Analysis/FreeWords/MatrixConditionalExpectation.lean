import Mathlib
import OAI.Analysis.FreeWords.ScalarAmalgamated

namespace OAI

noncomputable section

namespace KKMatrixExpectation

open KKAmalgamatedTransport

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def numericalHom (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) A :=
  { (Algebra.ofId ℂ A).mapMatrix with
    map_star' := by
      intro x
      ext i j
      exact map_star (StarAlgHom.ofId ℂ A) (x j i) }

@[simp] theorem numericalHom_apply (n : ℕ) (a : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    numericalHom (A := A) n a i j=algebraMap ℂ A (a i j) := rfl

def matrixTraceMap (τ : A →ₗ[ℂ] ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) A →ₗ[ℂ] ℂ :=
  (n:ℂ)⁻¹ • (Matrix.traceLinearMap (Fin n) ℂ ℂ).comp τ.mapMatrix

def matrixExpectation (τ : A →ₗ[ℂ] ℂ) (n : ℕ) :
    Matrix (Fin n) (Fin n) A →ₗ[ℂ] Matrix (Fin n) (Fin n) A :=
  (numericalHom (A := A) n).toLinearMap.comp τ.mapMatrix

@[simp] theorem matrixExpectation_apply (τ : A →ₗ[ℂ] ℂ) (n : ℕ)
    (x : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    matrixExpectation τ n x i j=algebraMap ℂ A (τ (x i j)) := rfl

omit [StarRing A] [StarModule ℂ A] in
@[simp] theorem matrixTraceMap_apply (τ : A →ₗ[ℂ] ℂ) (n : ℕ)
    (x : Matrix (Fin n) (Fin n) A) :
    matrixTraceMap τ n x=(n:ℂ)⁻¹*∑i,τ (x i i) := rfl

omit [StarRing A] [StarModule ℂ A] in
theorem trace_algebraMap (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1=1) (z : ℂ) :
    τ (algebraMap ℂ A z)=z := by
  rw [Algebra.algebraMap_eq_smul_one,map_smul,hτ1,smul_eq_mul,mul_one]

theorem matrixTraceMap_numerical (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1=1) (n : ℕ)
    (z : Matrix (Fin n) (Fin n) ℂ) :
    matrixTraceMap τ n (numericalHom (A := A) n z)=(n:ℂ)⁻¹*Matrix.trace z := by
  simp only [matrixTraceMap_apply,numericalHom_apply,trace_algebraMap τ hτ1,Matrix.trace,Matrix.diag]

theorem matrixTraceMap_one (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1=1) {n : ℕ} (hn : 0<n) :
    matrixTraceMap τ n 1=1 := by
  rw [← map_one (numericalHom (A := A) n),matrixTraceMap_numerical τ hτ1,Matrix.trace_one]
  simp only [Fintype.card_fin]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')

theorem matrixExpectation_range (τ : A →ₗ[ℂ] ℂ) (n : ℕ)
    (x : Matrix (Fin n) (Fin n) A) : matrixExpectation τ n x∈(numericalHom (A := A) n).range :=
  ⟨τ.mapMatrix x,rfl⟩

theorem matrixExpectation_fix (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1=1) (n : ℕ)
    (b : Matrix (Fin n) (Fin n) A) (hb : b∈(numericalHom (A := A) n).range) :
    matrixExpectation τ n b=b := by
  obtain ⟨z,rfl⟩ := hb
  change matrixExpectation τ n (numericalHom (A := A) n z)=numericalHom (A := A) n z
  ext i j
  simp only [matrixExpectation_apply,numericalHom_apply,trace_algebraMap τ hτ1]

theorem matrixExpectation_right (τ : A →ₗ[ℂ] ℂ) (n : ℕ)
    (a b : Matrix (Fin n) (Fin n) A) (hb : b∈(numericalHom (A := A) n).range) :
    matrixExpectation τ n (a*b)=matrixExpectation τ n a*b := by
  obtain ⟨z,rfl⟩ := hb
  change matrixExpectation τ n (a*numericalHom (A := A) n z)=matrixExpectation τ n a*numericalHom (A := A) n z
  ext i j
  simp only [matrixExpectation_apply,Matrix.mul_apply,numericalHom_apply,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show a i k*algebraMap ℂ A (z k j)=(z k j) • a i k by
    rw [Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one]]
  rw [map_smul,smul_eq_mul,mul_comm (z k j),map_mul]

theorem matrixExpectation_trace (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1=1) (n : ℕ)
    (a : Matrix (Fin n) (Fin n) A) :
    matrixTraceMap τ n (matrixExpectation τ n a)=matrixTraceMap τ n a := by
  simp only [matrixTraceMap_apply,matrixExpectation_apply,trace_algebraMap τ hτ1]

theorem matrixTraceMap_faithful_numerical (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1=1)
    {n : ℕ} (hn : 0<n) (b : Matrix (Fin n) (Fin n) A)
    (hb : b∈(numericalHom (A := A) n).range) (hzero : matrixTraceMap τ n (b*star b)=0) : b=0 := by
  obtain ⟨z,rfl⟩ := hb
  change matrixTraceMap τ n (numericalHom (A := A) n z*star (numericalHom (A := A) n z))=0 at hzero
  change numericalHom (A := A) n z=0
  rw [← map_star,← map_mul,matrixTraceMap_numerical τ hτ1] at hzero
  have hz : Matrix.trace (z*star z)=0 := (mul_eq_zero.mp hzero).resolve_left
    (inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne'))
  have hz' : z=0 := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hz
  rw [hz',map_zero]

theorem matrix_scalar_amalgamated_cyclic_transport (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1=1)
    {n : ℕ} (hn : 0<n) (C P Q : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) A))
    (hBP : (numericalHom (A := A) n).range≤P) (hBQ : (numericalHom (A := A) n).range≤Q) (hCQ : C≤Q)
    (hscalar : AlternatingMoments (matrixTraceMap τ n)
      (Centered (matrixTraceMap τ n) C) (Centered (matrixTraceMap τ n) (numericalHom (A := A) n).range))
    (hrelative : AlternatingMoments (matrixExpectation τ n)
      (RelativeCentered (matrixExpectation τ n) Q) (RelativeCentered (matrixExpectation τ n) P))
    (w : List (Matrix (Fin n) (Fin n) A × Matrix (Fin n) (Fin n) A)) (hne : w≠[])
    (hw : ∀z∈w,z.1∈Centered (matrixTraceMap τ n) C ∧ z.2∈Centered (matrixTraceMap τ n) P) :
    matrixTraceMap τ n (pairProd w)=0 := by
  exact scalar_amalgamated_cyclic_transport (A := Matrix (Fin n) (Fin n) A) (matrixTraceMap τ n) (matrixExpectation τ n)
    (numericalHom (A := A) n).range C P Q (matrixTraceMap_one τ hτ1 hn) hBP hBQ hCQ
    (matrixExpectation_range τ n) (matrixExpectation_fix τ hτ1 n)
    (matrixExpectation_right τ n) (matrixExpectation_trace τ hτ1 n)
    (matrixTraceMap_faithful_numerical τ hτ1 hn) hscalar hrelative w hne hw

end

end KKMatrixExpectation
end

end OAI
