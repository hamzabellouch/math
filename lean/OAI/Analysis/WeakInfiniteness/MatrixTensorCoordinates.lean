import Mathlib
import OAI.Analysis.WeakInfiniteness.NuclearTensorMap

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

open scoped TensorProduct CStarAlgebra ComplexOrder

universe u

section

variable {n : Type*} [Fintype n] [DecidableEq n]
  {C : Type u} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

def scalarMatrixRep : CStarMatrix n n ℂ →⋆ₙₐ[ℂ]
    (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
  matrixOperatorHom.comp (CStarMatrix.mapₙₐ
    (StarAlgHom.ofId ℂ (ℂ →L[ℂ] ℂ)).toNonUnitalStarAlgHom)

lemma scalarMatrixRep_basis (M : CStarMatrix n n ℂ) (i j : n) :
    scalarMatrixRep M ((EuclideanSpace.basisFun n ℂ) j) i=M i j := by
  rw [EuclideanSpace.basisFun_apply]
  change matrixOperator (CStarMatrix.mapₙₐ
    (StarAlgHom.ofId ℂ (ℂ →L[ℂ] ℂ)).toNonUnitalStarAlgHom M) (PiLp.single 2 j 1) i=_
  rw [matrixOperator_single]
  simp [Algebra.algebraMap_eq_smul_one]

def matrixTensorCoefficient (M : CStarMatrix n n ℂ) (c : C) : CStarMatrix n n C :=
  CStarMatrix.ofMatrix (fun i j => M i j • c)

omit [PartialOrder C] [StarOrderedRing C] in
lemma matrixTensorCoefficient_eq (M : CStarMatrix n n ℂ) (c : C) :
    matrixTensorCoefficient M c=tensorCoefficientMatrix (EuclideanSpace.basisFun n ℂ) (scalarMatrixRep M) c := by
  ext i j
  change M i j • c = (EuclideanSpace.basisFun n ℂ).repr (scalarMatrixRep M ((EuclideanSpace.basisFun n ℂ) j)) i • c
  rw [EuclideanSpace.basisFun_repr,scalarMatrixRep_basis]

lemma norm_matrixTensorSum_le {ι : Type*} (s : Finset ι)
    (M : ι → CStarMatrix n n ℂ) (c : ι → C) :
    ‖∑ i ∈ s,matrixTensorCoefficient (M i) (c i)‖ ≤
      ‖∑ i ∈ s,spatialElementary (M i) (c i)‖ := by
  obtain ⟨H,ρ,hρ⟩ := exists_faithful_representation C
  have hi : Function.Injective (CStarMatrix.mapₙₐ (n := n) ρ) := by
    intro X Y hXY
    ext i j
    exact hρ (congrArg (fun Z : CStarMatrix n n (H →L[ℂ] H) => Z i j) hXY)
  rw [← NonUnitalStarAlgHom.norm_map (CStarMatrix.mapₙₐ ρ) hi]
  simp only [map_sum,matrixTensorCoefficient_eq,map_tensorCoefficientMatrix]
  rw [← norm_tensorCoefficientSum]
  exact norm_tensorSum_le_spatial_any s M c scalarMatrixRep ρ

def matrixTensorPolynomial : (CStarMatrix n n ℂ × C →₀ ℂ) →ₗ[ℂ] CStarMatrix n n C :=
  Finsupp.linearCombination ℂ (fun p => matrixTensorCoefficient p.1 p.2)

lemma norm_matrixTensorPolynomial_le (d : CStarMatrix n n ℂ × C →₀ ℂ) :
    ‖matrixTensorPolynomial d‖ ≤ 1*‖tensorPolynomial d‖ := by
  classical
  rw [one_mul]
  change ‖d.sum (fun p t => t • matrixTensorCoefficient p.1 p.2)‖ ≤
    ‖(minimalTensorSubalgebra (CStarMatrix n n ℂ) C).subtype
      (d.sum fun p t => t • minimalElementary p.1 p.2)‖
  simp only [Finsupp.sum,map_sum,map_smul]
  change ‖∑ p ∈ d.support,d p • matrixTensorCoefficient p.1 p.2‖ ≤
    ‖∑ p ∈ d.support,d p • spatialElementary p.1 p.2‖
  have hs (t : ℂ) (M : CStarMatrix n n ℂ) (c : C) :
      matrixTensorCoefficient (t • M) c=t • matrixTensorCoefficient M c := by
    ext i j
    exact mul_smul t (M i j) c
  simpa only [spatialElementary_smul_left,hs] using
    norm_matrixTensorSum_le d.support (fun p => d p • p.1) Prod.snd

def matrixTensorCoordinates : MinimalTensor (CStarMatrix n n ℂ) C →L[ℂ] CStarMatrix n n C :=
  matrixTensorPolynomial.extendOfNorm tensorPolynomial

lemma matrixTensorCoordinates_polynomial (d : CStarMatrix n n ℂ × C →₀ ℂ) :
    matrixTensorCoordinates (tensorPolynomial d)=matrixTensorPolynomial d :=
  LinearMap.extendOfNorm_eq (tensorPolynomial_dense (A := CStarMatrix n n ℂ) (C := C))
    ⟨1,norm_matrixTensorPolynomial_le (n := n) (C := C)⟩ d

lemma matrixTensorCoordinates_elementary (M : CStarMatrix n n ℂ) (c : C) :
    matrixTensorCoordinates (minimalElementary M c)=matrixTensorCoefficient M c := by
  rw [← tensorPolynomial_single M c,matrixTensorCoordinates_polynomial]
  simp [matrixTensorPolynomial]

end

end

end WeakPureInfiniteness
end

end OAI
