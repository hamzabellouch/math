import Mathlib
import OAI.Analysis.Commutator.MatrixProjectionDiagonal

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace Kadison.MatrixCorners

variable {I J K : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

attribute [local instance] Classical.propDecidable

omit [DecidableEq I] [DecidableEq J] in
lemma trace_reindex (e : J ≃ I) (a : Matrix J J ℂ) :
    (Matrix.reindex e e a).trace=a.trace := by
  exact e.symm.sum_comp (fun j => a j j)

omit [DecidableEq J] [DecidableEq K] in
lemma trace_cutBlock (a : Matrix J J ℂ) :
    (Matrix.fromBlocks a (0:Matrix J K ℂ) 0 0).trace=a.trace := by
  simp [Matrix.trace,Fintype.sum_sum_type]

def cutBlock : Matrix J J ℂ →⋆ₙₐ[ℂ] Matrix (J⊕K) (J⊕K) ℂ where
  toFun a := Matrix.fromBlocks a 0 0 0
  map_zero' := by ext i j; cases i <;> cases j <;> rfl
  map_add' a b := by ext i j; cases i <;> cases j <;> simp
  map_smul' c a := by ext i j; cases i <;> cases j <;> simp
  map_mul' a b := by simp [Matrix.fromBlocks_multiply]
  map_star' a := by
    change _= (Matrix.fromBlocks a (0:Matrix J K ℂ) 0 0).conjTranspose
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero]
    rfl

def reindexStarAlgEquiv (e : J ≃ I) : Matrix J J ℂ ≃⋆ₐ[ℂ] Matrix I I ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_smul' := fun c a => by ext i j; rfl
    map_star' := fun a => by exact (Matrix.conjTranspose_reindex e e a).symm }

def cutEmbedding (s : Set I) : Matrix s s ℂ →⋆ₙₐ[ℂ] Matrix I I ℂ :=
  (reindexStarAlgEquiv (Equiv.Set.sumCompl s)).toNonUnitalStarAlgHom.comp
    (cutBlock (K := (sᶜ:Set I)))

lemma cutEmbedding_trace (s : Set I) (a : Matrix s s ℂ) :
    (cutEmbedding s a).trace=a.trace := by
  change (Matrix.reindex (Equiv.Set.sumCompl s) (Equiv.Set.sumCompl s)
    (Matrix.fromBlocks a (0:Matrix s (sᶜ:Set I) ℂ) 0 0)).trace=a.trace
  rw [trace_reindex,trace_cutBlock]

lemma cutEmbedding_one (s : Set I) :
    cutEmbedding s 1=Matrix.diagonal (fun i => if i∈s then (1:ℂ) else 0) := by
  ext i j
  by_cases hi : i∈s <;> by_cases hj : j∈s
  · change Matrix.fromBlocks (1:Matrix s s ℂ) 0 0 0
      ((Equiv.Set.sumCompl s).symm i) ((Equiv.Set.sumCompl s).symm j)=_
    rw [Equiv.Set.sumCompl_symm_apply_of_mem hi,Equiv.Set.sumCompl_symm_apply_of_mem hj]
    simp [Matrix.one_apply,Matrix.diagonal_apply,hi]
  · change Matrix.fromBlocks (1:Matrix s s ℂ) 0 0 0
      ((Equiv.Set.sumCompl s).symm i) ((Equiv.Set.sumCompl s).symm j)=_
    rw [Equiv.Set.sumCompl_symm_apply_of_mem hi,Equiv.Set.sumCompl_symm_apply_of_notMem hj]
    simp [show i≠j from fun h=>hj (h ▸ hi)]
  · change Matrix.fromBlocks (1:Matrix s s ℂ) 0 0 0
      ((Equiv.Set.sumCompl s).symm i) ((Equiv.Set.sumCompl s).symm j)=_
    rw [Equiv.Set.sumCompl_symm_apply_of_notMem hi,Equiv.Set.sumCompl_symm_apply_of_mem hj]
    simp [Matrix.diagonal_apply,hi]
  · change Matrix.fromBlocks (1:Matrix s s ℂ) 0 0 0
      ((Equiv.Set.sumCompl s).symm i) ((Equiv.Set.sumCompl s).symm j)=_
    rw [Equiv.Set.sumCompl_symm_apply_of_notMem hi,Equiv.Set.sumCompl_symm_apply_of_notMem hj]
    simp [Matrix.diagonal_apply,hi]

def projectionEmbedding (p : Matrix I I ℂ) (hp : IsStarProjection p) :
    Matrix (projectionIndices p hp) (projectionIndices p hp) ℂ →⋆ₙₐ[ℂ] Matrix I I ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ)
    (projection_hermitian p hp).eigenvectorUnitary).toNonUnitalStarAlgHom.comp
      (cutEmbedding (projectionIndices p hp))

lemma projectionEmbedding_one (p : Matrix I I ℂ) (hp : IsStarProjection p) :
    projectionEmbedding p hp 1=p := by
  change Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) _ (cutEmbedding _ 1)=p
  rw [cutEmbedding_one]
  exact (projection_diagonal_form p hp).symm

lemma projectionEmbedding_trace (p : Matrix I I ℂ) (hp : IsStarProjection p)
    (a : Matrix (projectionIndices p hp) (projectionIndices p hp) ℂ) :
    (projectionEmbedding p hp a).trace=a.trace := by
  change (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) _ (cutEmbedding _ a)).trace=a.trace
  rw [trace_conjugation,cutEmbedding_trace]

end Kadison.MatrixCorners

end

end
end

end OAI
