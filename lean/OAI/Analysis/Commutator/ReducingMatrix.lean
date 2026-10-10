import Mathlib
import OAI.Analysis.Commutator.MainMatrix
import OAI.Analysis.Commutator.ReducingCompression

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def matrixInclusion (K : Submodule ℂ H) (h : ℕ) :
    (PiLp 2 fun _ : Fin h => K) →ₗᵢ[ℂ] (PiLp 2 fun _ : Fin h => H) where
  toFun x := WithLp.toLp 2 (fun i => (x i:H))
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl
  norm_map' x := by
    rw [PiLp.norm_eq_of_L2,PiLp.norm_eq_of_L2]
    rfl

omit [CompleteSpace H] in
@[simp] lemma matrixInclusion_apply (K : Submodule ℂ H) (h : ℕ)
    (x : PiLp 2 fun _ : Fin h => K) (i : Fin h) : matrixInclusion K h x i=(x i:H) := rfl

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H),x∈K → σ a x∈K)

lemma matrix_intertwines (h : ℕ) (X : Matrix (Fin h) (Fin h) A) :
    (matrixOperator h (fun i j => σ (X i j))).comp (matrixInclusion K h).toContinuousLinearMap=
    (matrixInclusion K h).toContinuousLinearMap.comp
      (matrixOperator h (fun i j => restrict σ K hinv (X i j))) := by
  ext x i
  change (matrixOperator h (fun i j => σ (X i j)) (matrixInclusion K h x)) i=
    ((matrixOperator h (fun i j => restrict σ K hinv (X i j)) x) i:H)
  erw [matrixOperator_apply,matrixOperator_apply]
  exact (map_sum K.subtype (fun j => restrict σ K hinv (X i j) (x j)) Finset.univ).symm

lemma restricted_matrix_norm_le (h : ℕ) (X : Matrix (Fin h) (Fin h) A) :
    ‖matrixOperator h (fun i j => restrict σ K hinv (X i j))‖≤
      ‖matrixOperator h (fun i j => σ (X i j))‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have he := congrArg (fun T => T x) (matrix_intertwines σ K hinv h X)
  change matrixOperator h (fun i j => σ (X i j)) (matrixInclusion K h x)=
    matrixInclusion K h (matrixOperator h (fun i j => restrict σ K hinv (X i j)) x) at he
  rw [←(matrixInclusion K h).norm_map,←he]
  simpa only [LinearIsometry.norm_map] using
    (matrixOperator h (fun i j => σ (X i j))).le_opNorm (matrixInclusion K h x)

omit [CompleteSpace H] [CompleteSpace K] in
lemma diagonal_intertwines (Y : H →L[ℂ] H) (hY : ∀ x∈K,Y x∈K) (h : ℕ) :
    (diagonalAmplification h Y).comp (matrixInclusion K h).toContinuousLinearMap=
      (matrixInclusion K h).toContinuousLinearMap.comp (diagonalAmplification h (Y.restrict hY)) := by
  ext x i
  rfl

lemma matrix_commutator_intertwines (Y : H →L[ℂ] H) (hY : ∀ x∈K,Y x∈K)
    (h : ℕ) (X : Matrix (Fin h) (Fin h) A) :
    (diagonalAmplification h Y*matrixOperator h (fun i j => σ (X i j))-
      matrixOperator h (fun i j => σ (X i j))*diagonalAmplification h Y).comp
        (matrixInclusion K h).toContinuousLinearMap=
    (matrixInclusion K h).toContinuousLinearMap.comp
      (diagonalAmplification h (Y.restrict hY)*matrixOperator h (fun i j => restrict σ K hinv (X i j))-
       matrixOperator h (fun i j => restrict σ K hinv (X i j))*diagonalAmplification h (Y.restrict hY)) := by
  simp only [sub_comp,comp_sub,mul_def]
  congr 1
  · rw [comp_assoc,matrix_intertwines σ K hinv h X,←comp_assoc,
      diagonal_intertwines K Y hY h,comp_assoc]
  · rw [comp_assoc,diagonal_intertwines K Y hY h,←comp_assoc,
      matrix_intertwines σ K hinv h X,comp_assoc]

omit [CompleteSpace H] in
lemma compression_eq_restrict (Y : H →L[ℂ] H) (hY : ∀ x∈K,Y x∈K) :
    compression K Y=Y.restrict hY := by
  apply ContinuousLinearMap.ext
  intro x
  change K.orthogonalProjectionOnto (Y (x:H))=(Y.restrict hY) x
  exact K.orthogonalProjectionOnto_mem_subspace_eq_self (Y.restrict hY x)

end Kadison.ReducingRepresentation

end

end
end

end OAI
