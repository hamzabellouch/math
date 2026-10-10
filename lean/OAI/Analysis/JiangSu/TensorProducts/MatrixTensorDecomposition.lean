import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropSquare

namespace OAI

section

noncomputable section
namespace MatrixTensor
open scoped Kronecker CStarAlgebra TensorProduct

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def single (i k : I) (z : ℂ) : Mat I := CStarMatrix.ofMatrix (Matrix.single i k z)

lemma single_tensor (i k : I) (j l : J) (z : ℂ) :
    single (i,j) (k,l) z=left (single i k z)*right (single j l 1) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  rw [left_mul_right_apply]
  change Matrix.single (i,j) (k,l) z (a,b) (c,d)=
    Matrix.single i k z a c*Matrix.single j l 1 b d
  by_cases hi : i=a <;> by_cases hk : k=c <;> by_cases hj : j=b <;> by_cases hl : l=d <;>
    simp [Matrix.single,hi,hk,hj,hl]

lemma matrix_eq_sum_single (x : Mat I) : x=∑ i,∑ k,single i k (x i k) := by
  apply (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.injective
  simp only [map_sum]
  exact Matrix.matrix_eq_sum_single _

lemma mem_of_pure_tensors (S : StarSubalgebra ℂ (Mat (I×J)))
    (h : ∀ a : Mat I,∀ b : Mat J,left a*right b∈S) (x : Mat (I×J)) : x∈S := by
  rw [matrix_eq_sum_single x]
  apply S.sum_mem
  rintro ⟨i,j⟩ _
  apply S.sum_mem
  rintro ⟨k,l⟩ _
  rw [single_tensor]
  exact h _ _

lemma fiberAlgebra_top_top : fiberAlgebra (⊤ : StarSubalgebra ℂ (Mat I))
    (⊤ : StarSubalgebra ℂ (Mat J))=⊤ := by
  apply top_unique
  intro x _
  exact mem_of_pure_tensors _ (fun a b => mul_mem_fiber _ _ (by trivial) (by trivial)) x

lemma left_mem_fiber (S : StarSubalgebra ℂ (Mat I)) (T : StarSubalgebra ℂ (Mat J))
    {a : Mat I} (ha : a∈S) : left (J := J) a∈fiberAlgebra S T := by
  simpa only [map_one,mul_one] using mul_mem_fiber S T ha (one_mem T)
lemma right_mem_fiber (S : StarSubalgebra ℂ (Mat I)) (T : StarSubalgebra ℂ (Mat J))
    {b : Mat J} (hb : b∈T) : right (I := I) b∈fiberAlgebra S T := by
  simpa only [map_one,one_mul] using mul_mem_fiber S T (one_mem S) hb

lemma fiberAlgebra_mono {S S' : StarSubalgebra ℂ (Mat I)} {T T' : StarSubalgebra ℂ (Mat J)}
    (hS : S≤S') (hT : T≤T') : fiberAlgebra S T≤fiberAlgebra S' T' := by
  intro x hx
  obtain ⟨n,a,b,rfl⟩ := fiber_finite_sum S T hx
  apply (fiberAlgebra S' T').sum_mem
  intro index _
  exact mul_mem_fiber S' T' (hS (a index).property) (hT (b index).property)
end MatrixTensor

namespace JiangSuConstruction
open scoped CStarAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]
@[simp] lemma permutationUnitary_one : permutationUnitary (1 : Equiv.Perm I)=1 := by
  apply Subtype.ext
  change CStarMatrix.ofMatrix ((1 : Equiv.Perm I)⁻¹.permMatrix ℂ)=1
  simp only [inv_one,Matrix.permMatrix_one]
  rfl
lemma permutationUnitary_mul (e f : Equiv.Perm I) :
    permutationUnitary (e*f)=permutationUnitary e*permutationUnitary f := by
  apply Subtype.ext
  change CStarMatrix.ofMatrix ((e*f)⁻¹.permMatrix ℂ)=
    CStarMatrix.ofMatrix (e⁻¹.permMatrix ℂ)*CStarMatrix.ofMatrix (f⁻¹.permMatrix ℂ)
  rw [mul_inv_rev,Matrix.permMatrix_mul]
  rfl
lemma permutationUnitary_apply (e : Equiv.Perm I) (i j : I) :
    (permutationUnitary e : CStarMatrix I I ℂ) i j=if e j=i then 1 else 0 := by
  change (e⁻¹).toPEquiv.toMatrix i j=_
  by_cases h : e j=i
  · have hi : e.symm i=j := by
      rw [←h]
      simp
    simp [PEquiv.toMatrix,Equiv.toPEquiv,h,hi]
  · have hi : e.symm i≠j := by
      intro hh
      apply h
      rw [←hh]
      simp
    simp [PEquiv.toMatrix,Equiv.toPEquiv,h,hi]

end JiangSuConstruction

end
end

end OAI
