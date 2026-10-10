import Mathlib
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorBound
import OAI.Analysis.WeakInfiniteness.NuclearCP

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

open scoped CStarAlgebra TensorProduct ENNReal

section

variable {A B n H K L : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [Fintype n] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma matrixLinearMap_tensorCoefficient (φ : A →L[ℂ] B)
    (b : OrthonormalBasis n ℂ H) (T : H →L[ℂ] H) (a : A) :
    matrixLinearMap φ (tensorCoefficientMatrix b T a)=tensorCoefficientMatrix b T (φ a) := by
  ext i j
  exact map_smul φ _ _

lemma tensor_norm_cp_finite_left {ι : Type*} (s : Finset ι)
    (b : OrthonormalBasis n ℂ H) (T : ι → H →L[ℂ] H) (a : ι → A)
    (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (π : B →⋆ₙₐ[ℂ] (L →L[ℂ] L))
    (hρ : Function.Injective ρ) :
    ‖∑ i ∈ s, TensorProduct.mapL (T i) (π (φ (a i)))‖ ≤
      (4*‖φ‖)*‖∑ i ∈ s,TensorProduct.mapL (T i) (ρ (a i))‖ := by
  classical
  rw [norm_tensorCoefficientSum s b,norm_tensorCoefficientSum s b]
  let M : CStarMatrix n n A := ∑ i ∈ s,tensorCoefficientMatrix b (T i) (a i)
  have hf : CStarMatrix.mapₙₐ π (matrixLinearMap φ M)=
      ∑ i ∈ s,tensorCoefficientMatrix b (T i) (π (φ (a i))) := by
    simp only [M,map_sum,matrixLinearMap_tensorCoefficient,map_tensorCoefficientMatrix]
  have hr : CStarMatrix.mapₙₐ ρ M=∑ i ∈ s,tensorCoefficientMatrix b (T i) (ρ (a i)) := by
    simp only [M,map_sum,map_tensorCoefficientMatrix]
  rw [← hf,← hr]
  have hi : Function.Injective (CStarMatrix.mapₙₐ (n := n) ρ) := by
    intro X Y hXY
    ext i j
    exact hρ (congrArg (fun Z : CStarMatrix n n (K →L[ℂ] K) => Z i j) hXY)
  rw [NonUnitalStarAlgHom.norm_map _ hi]
  exact (NonUnitalStarAlgHom.norm_apply_le _ _).trans (norm_matrixLinearMap_le hφ M)

omit [Fintype n] in
lemma tensor_norm_cp {ι : Type*} [Finite ι] (s : Finset ι)
    (T : ι → H →L[ℂ] H) (a : ι → A)
    (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (π : B →⋆ₙₐ[ℂ] (L →L[ℂ] L))
    (hρ : Function.Injective ρ) :
    ‖∑ i ∈ s,TensorProduct.mapL (T i) (π (φ (a i)))‖ ≤
      (4*‖φ‖)*‖∑ i ∈ s,TensorProduct.mapL (T i) (ρ (a i))‖ := by
  apply norm_tensorSum_le_of_finite_compressions s T (fun i => π (φ (a i))) (by positivity)
  intro V hV
  exact (tensor_norm_cp_finite_left s (stdOrthonormalBasis ℂ V)
    (fun i => compress V (T i)) a φ hφ ρ π hρ).trans
    (mul_le_mul_of_nonneg_left (norm_tensorSum_compress_le s V T (fun i => ρ (a i))) (by positivity))

omit [Fintype n] in
lemma tensor_norm_cp_finset {ι : Type*} (s : Finset ι)
    (T : ι → H →L[ℂ] H) (a : ι → A)
    (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (π : B →⋆ₙₐ[ℂ] (L →L[ℂ] L))
    (hρ : Function.Injective ρ) :
    ‖∑ i ∈ s,TensorProduct.mapL (T i) (π (φ (a i)))‖ ≤
      (4*‖φ‖)*‖∑ i ∈ s,TensorProduct.mapL (T i) (ρ (a i))‖ := by
  classical
  rw [← Finset.sum_coe_sort s (fun i => TensorProduct.mapL (T i) (π (φ (a i)))),
    ← Finset.sum_coe_sort s (fun i => TensorProduct.mapL (T i) (ρ (a i)))]
  exact tensor_norm_cp Finset.univ (fun i : s => T i) (fun i : s => a i) φ hφ ρ π hρ

end

lemma norm_spatialSum_cp {A B C : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    {ι : Type*} (s : Finset ι) (a : ι → A) (c : ι → C)
    (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ) :
    ‖∑ i ∈ s,spatialElementary (φ (a i)) (c i)‖ ≤
      (4*‖φ‖)*‖∑ i ∈ s,spatialElementary (a i) (c i)‖ := by
  obtain ⟨H,ρ,hρ⟩ := exists_faithful_representation A
  apply lp.norm_le_of_forall_le (by positivity)
  intro π
  rw [spatialSum_apply,norm_completion,norm_tensorSum_flip]
  apply (tensor_norm_cp_finset s (fun i => π.rightRep (c i)) a φ hφ ρ π.leftRep hρ).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [norm_tensorSum_flip]
  exact norm_tensorSum_le_spatial_any s a c ρ π.rightRep

end

end WeakPureInfiniteness
end

end OAI
