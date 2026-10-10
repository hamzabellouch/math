import Mathlib
import OAI.Analysis.WeakInfiniteness.MatrixTensorCoordinates

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra ComplexOrder

universe u

section

variable {n : Type*} [Fintype n] [DecidableEq n]
  {C D : Type u} [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
  [PartialOrder C] [StarOrderedRing C] [PartialOrder D] [StarOrderedRing D]

def matrixEntryLinear (i j : n) : CStarMatrix n n C →ₗ[ℂ] C where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def matrixUnit (i j : n) : CStarMatrix n n ℂ :=
  CStarMatrix.ofMatrix (fun k l => if k=i ∧ l=j then 1 else 0)

lemma matrix_unit_expansion (M : CStarMatrix n n ℂ) :
    (∑ i,∑ j,M i j • matrixUnit i j)=M := by
  ext k l
  change matrixEntryLinear k l (∑ i,∑ j,M i j • matrixUnit i j)=M k l
  simp only [map_sum,map_smul]
  change (∑ i,∑ j,M i j * (if k=i ∧ l=j then 1 else 0))=M k l
  simp [ite_and]

def matrixEntryContinuous (i j : n) : CStarMatrix n n C →L[ℂ] C :=
  (matrixEntryLinear i j).mkContinuous 1 (fun M => by
    change ‖M i j‖ ≤ 1*‖M‖
    simpa only [one_mul] using (CStarMatrix.norm_entry_le_norm (M := M) (i := i) (j := j)))

def matrixTensorReconstruct : CStarMatrix n n C →L[ℂ] MinimalTensor (CStarMatrix n n ℂ) C :=
  ∑ i,∑ j,(minimalElementaryRightContinuous (matrixUnit i j)).comp (matrixEntryContinuous i j)

lemma matrixTensorReconstruct_apply (M : CStarMatrix n n C) :
    matrixTensorReconstruct M=∑ i,∑ j,minimalElementary (matrixUnit i j) (M i j) := by
  simp only [matrixTensorReconstruct,sum_apply,ContinuousLinearMap.comp_apply]
  rfl

lemma minimalElementary_balance {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (t : ℂ) (a : A) (b : B) : minimalElementary a (t • b)=minimalElementary (t • a) b := by
  apply Subtype.ext
  exact (spatialElementary_smul_right t a b).trans (spatialElementary_smul_left t a b).symm

lemma matrixTensorReconstruct_coefficient (M : CStarMatrix n n ℂ) (c : C) :
    matrixTensorReconstruct (matrixTensorCoefficient M c)=minimalElementary M c := by
  rw [matrixTensorReconstruct_apply]
  change (∑ i,∑ j,minimalElementary (matrixUnit i j) (M i j • c))=minimalElementary M c
  simp only [minimalElementary_balance]
  change (∑ i,∑ j,minimalElementaryLeftLinear c (M i j • matrixUnit i j))=minimalElementaryLeftLinear c M
  simpa only [map_sum] using congrArg (minimalElementaryLeftLinear c) (matrix_unit_expansion M)

lemma matrixTensorReconstruct_coordinates (z : MinimalTensor (CStarMatrix n n ℂ) C) :
    matrixTensorReconstruct (matrixTensorCoordinates z)=z := by
  have he : (matrixTensorReconstruct (n := n) (C := C)).comp matrixTensorCoordinates=
      ContinuousLinearMap.id ℂ (MinimalTensor (CStarMatrix n n ℂ) C) := by
    apply minimalTensor_clm_ext
    intro M c
    change matrixTensorReconstruct (matrixTensorCoordinates (minimalElementary M c))=minimalElementary M c
    rw [matrixTensorCoordinates_elementary,matrixTensorReconstruct_coefficient]
  exact DFunLike.congr_fun he z

lemma matrixTensorCoordinates_right_comm (q : C →⋆ₙₐ[ℂ] D)
    (z : MinimalTensor (CStarMatrix n n ℂ) C) :
    CStarMatrix.mapₙₐ q (matrixTensorCoordinates z)=matrixTensorCoordinates (minimalMapRight q z) := by
  let f : CStarMatrix n n C →L[ℂ] CStarMatrix n n D := starHomContinuousLinear (CStarMatrix.mapₙₐ q)
  let g : MinimalTensor (CStarMatrix n n ℂ) C →L[ℂ] MinimalTensor (CStarMatrix n n ℂ) D :=
    starHomContinuousLinear (minimalMapRight q)
  let F : MinimalTensor (CStarMatrix n n ℂ) C →L[ℂ] CStarMatrix n n C := matrixTensorCoordinates
  let G : MinimalTensor (CStarMatrix n n ℂ) D →L[ℂ] CStarMatrix n n D := matrixTensorCoordinates
  have he : f.comp F=G.comp g := by
    apply minimalTensor_clm_ext
    intro M c
    change CStarMatrix.mapₙₐ q (matrixTensorCoordinates (minimalElementary M c))=
      matrixTensorCoordinates (minimalMapRight q (minimalElementary M c))
    rw [matrixTensorCoordinates_elementary,minimalMapRight_elementary,matrixTensorCoordinates_elementary]
    ext i j
    exact map_smul q (M i j) c
  exact DFunLike.congr_fun he z

lemma matrixTensor_kernel (q : C →⋆ₙₐ[ℂ] D) (z : MinimalTensor (CStarMatrix n n ℂ) C)
    (hz : minimalMapRight q z=0) :
    z.val ∈ tensorKernelIdeal (A := CStarMatrix n n ℂ) q := by
  have hm : CStarMatrix.mapₙₐ q (matrixTensorCoordinates z)=0 := by
    rw [matrixTensorCoordinates_right_comm,hz,map_zero]
  rw [← matrixTensorReconstruct_coordinates z,matrixTensorReconstruct_apply]
  change (minimalTensorSubalgebra (CStarMatrix n n ℂ) C).subtype
    (∑ i,∑ j,minimalElementary (matrixUnit i j) (matrixTensorCoordinates z i j)) ∈ _
  simp only [map_sum]
  apply (tensorKernelIdeal (A := CStarMatrix n n ℂ) q).toSubmodule.sum_mem
  intro i _
  apply (tensorKernelIdeal (A := CStarMatrix n n ℂ) q).toSubmodule.sum_mem
  intro j _
  apply NonUnitalStarSubalgebra.le_topologicalClosure
  apply NonUnitalStarAlgebra.subset_adjoin
  exact ⟨matrixUnit i j,matrixTensorCoordinates z i j,
    congrArg (fun M : CStarMatrix n n D => M i j) hm,rfl⟩

end

end

end WeakPureInfiniteness
end

end OAI
