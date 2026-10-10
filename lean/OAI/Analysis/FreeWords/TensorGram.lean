import Mathlib
import OAI.Analysis.FreeWords.TensorCalculus
import OAI.Analysis.FreeWords.TensorLieSpan

namespace OAI

noncomputable section

namespace KKWeingarten

open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

theorem positionMatrix_tensorMatrix_commute {r d : ℕ} (π : Equiv.Perm (Fin r))
    (U : Matrix (Fin d) (Fin d) ℂ) : Commute (positionMatrix (d := d) π) (tensorMatrix U) := by
  classical
  ext a b
  have hh (c : Fin r → Fin d) : b=c ∘ π ↔ c=b ∘ π.symm := by
    constructor
    · intro he
      funext s
      have h := congrFun he (π.symm s)
      simpa only [Function.comp_apply,Equiv.apply_symm_apply] using h.symm
    · rintro rfl
      funext s
      simp
  simp only [Matrix.mul_apply,positionMatrix,hh]
  simp only [ite_mul,one_mul,zero_mul,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  unfold tensorMatrix
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using
    Equiv.prod_comp π (fun s => U (a s) (b (π.symm s)))

def positionVector {r d : ℕ} (π : Equiv.Perm (Fin r)) :
    EuclideanSpace ℂ ((Fin r → Fin d) × (Fin r → Fin d)) :=
  WithLp.toLp 2 (fun p => positionMatrix π p.1 p.2)

theorem positionVector_linearIndependent {r d : ℕ} (hrd : r ≤ d) :
    LinearIndependent ℂ (positionVector (r := r) (d := d)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let a : Fin r → Fin d := Fin.castLE hrd
  have ha : Function.Injective a := Fin.castLE_injective hrd
  intro σ
  have he (π : Equiv.Perm (Fin r)) : a ∘ σ=a ∘ π ↔ σ=π := by
    constructor
    · intro h
      apply Equiv.ext
      intro s
      exact ha (congrFun h s)
    · rintro rfl; rfl
  have hz := congrArg (fun v : EuclideanSpace ℂ ((Fin r → Fin d) × (Fin r → Fin d)) =>
    v (a,a ∘ σ)) hc
  simpa [positionVector,positionMatrix,he] using hz

def permutationGram (r d : ℕ) : Matrix (Equiv.Perm (Fin r)) (Equiv.Perm (Fin r)) ℂ :=
  Matrix.gram ℂ (positionVector (d := d))

theorem permutationGram_det_ne_zero {r d : ℕ} (hrd : r ≤ d) :
    (permutationGram r d).det ≠ 0 :=
  Matrix.det_gram_ne_zero_iff_linearIndependent.mpr (positionVector_linearIndependent hrd)

def matrixPair {ι : Type*} [Fintype ι] (S T : Matrix ι ι ℂ) : ℂ :=
  Matrix.trace (star S*T)

theorem matrixPair_apply {ι : Type*} [Fintype ι] (S T : Matrix ι ι ℂ) :
    matrixPair S T=∑ a,∑ b,star (S a b)*T a b := by
  simp only [matrixPair,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.star_apply]
  rw [Finset.sum_comm]

theorem permutationGram_apply {r d : ℕ} (π σ : Equiv.Perm (Fin r)) :
    permutationGram r d π σ=matrixPair (positionMatrix (d := d) π) (positionMatrix σ) := by
  rw [matrixPair_apply]
  simp [permutationGram,Matrix.gram_apply,positionVector,PiLp.inner_apply,
    RCLike.inner_apply,Fintype.sum_prod_type,mul_comm]

theorem matrixPair_sum_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix ι ι ℂ) (T : κ → Matrix ι ι ℂ) (c : κ → ℂ) :
    matrixPair S (∑ j,c j • T j)=∑ j,c j*matrixPair S (T j) := by
  simp [matrixPair,Matrix.mul_sum,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]

end

end KKWeingarten
end

end OAI
