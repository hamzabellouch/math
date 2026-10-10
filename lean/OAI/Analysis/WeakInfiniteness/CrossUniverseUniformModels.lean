import Mathlib
import OAI.Analysis.WeakInfiniteness.CrossUniverseLeftMap

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

open scoped TensorProduct

universe u

def FiniteContractionModelsAny (B : Type u) [CStarAlgebra B] (v : B) (θ : ℝ) : Prop :=
  ∀ (H : ComplexHilbert.{1}) [FiniteDimensional ℂ H] (D : H →L[ℂ] H), ‖D‖ ≤ 1 →
    ∃ K : ComplexHilbert.{u}, ∃ π : B →⋆ₐ[ℂ] (K →L[ℂ] K), ∃ J : H →ₗᵢ[ℂ] K,
      ‖(π v).comp J.toContinuousLinearMap - J.toContinuousLinearMap.comp D‖ ≤ θ ∧
      ‖(star (π v)).comp J.toContinuousLinearMap - J.toContinuousLinearMap.comp (star D)‖ ≤ θ

variable {B : Type u} {C : Type 1} [CStarAlgebra B] [NonUnitalCStarAlgebra C]

lemma minimalMapLeft_wordTensor_any (s : Finset (List Bool)) (c : List Bool → C)
    (φ : UniversalContraction →⋆ₐ[ℂ] B) :
    minimalMapLeftAny φ.toNonUnitalStarAlgHom (wordTensor s c) =
      ∑ w ∈ s, minimalElementary (φ (universalWord w)) (c w) := by
  rw [wordTensor, map_sum]
  apply Finset.sum_congr rfl
  intro w _hw
  exact minimalMapLeftAny_elementary φ.toNonUnitalStarAlgHom (universalWord w) (c w)

lemma norm_model_amplifiedPolynomial_le_any (s : Finset (List Bool)) (c : List Bool → C)
    (φ : UniversalContraction →⋆ₐ[ℂ] B) (K : ComplexHilbert.{1}) (L : ComplexHilbert.{u})
    (π : B →⋆ₐ[ℂ] (L →L[ℂ] L)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖amplifiedPolynomial s (fun w => σ (c w))
      (operatorLetters (π (φ universalContractionGenerator)))‖ ≤
      ‖minimalMapLeftAny φ.toNonUnitalStarAlgHom (wordTensor s c)‖ := by
  calc
    _ = ‖∑ w ∈ s, TensorProduct.mapL (π (φ (universalWord w))) (σ (c w))‖ := by
      rw [norm_tensorSum_flip]
      unfold amplifiedPolynomial
      congr 1
      apply Finset.sum_congr rfl
      intro w _hw
      congr 1
      exact (unitalRep_universalWord (π.comp φ) w).symm
    _ ≤ ‖∑ w ∈ s,spatialElementary (φ (universalWord w)) (c w)‖ :=
      norm_tensorSum_le_spatial_any s (fun w => φ (universalWord w)) c π.toNonUnitalStarAlgHom σ
    _ = _ := by
      rw [minimalMapLeft_wordTensor_any]
      change _ = ‖(minimalTensorSubalgebra B C).subtype
        (∑ w ∈ s,minimalElementary (φ (universalWord w)) (c w))‖
      rw [map_sum]
      rfl

lemma norm_faithfulAmplifiedPolynomial_le_of_models_any (s : Finset (List Bool)) (c : List Bool → C)
    (v : B) (hv : ‖v‖ ≤ 1) (φ : UniversalContraction →⋆ₐ[ℂ] B)
    (hφ : φ universalContractionGenerator = v) {θ : ℝ} (hθ : 0 ≤ θ)
    (hmodels : FiniteContractionModelsAny B v θ) (K : ComplexHilbert.{1})
    (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖amplifiedPolynomial s (fun w => σ (c w))
      (operatorLetters (universalUnitalRepresentation universalContractionGenerator))‖ ≤
      ‖minimalMapLeftAny φ.toNonUnitalStarAlgHom (wordTensor s c)‖ + wordTensorCost s c * θ := by
  have hM : 0 ≤ ‖minimalMapLeftAny φ.toNonUnitalStarAlgHom (wordTensor s c)‖ +
      wordTensorCost s c * θ := add_nonneg (norm_nonneg _) (mul_nonneg (wordTensorCost_nonneg s c) hθ)
  apply norm_amplifiedPolynomial_le_of_finite_compressions _ _ _ hM
  intro E hE
  let T := universalUnitalRepresentation universalContractionGenerator
  have hT : ‖T‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le universalUnitalRepresentation _).trans
    norm_universalContractionGenerator_le_one
  let H : ComplexHilbert.{1} := { Carrier := E }
  obtain ⟨L, π, J, hj, hjstar⟩ := hmodels H (compress E T) ((norm_compress_le E T).trans hT)
  have hJ : ∀ i : Bool, ‖(operatorLetters (π v) i).comp J.toContinuousLinearMap -
      J.toContinuousLinearMap.comp (operatorLetters (compress E T) i)‖ ≤ θ := by
    intro i
    cases i
    · exact hjstar
    · exact hj
  have hcomp : (fun i => compress E (operatorLetters T i)) = operatorLetters (compress E T) := by
    funext i
    exact (operatorLetters_compress E T i).symm
  rw [hcomp]
  have hπ : ‖π v‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le π v).trans hv
  have hb := norm_amplifiedPolynomial_le s (fun w => σ (c w))
    (operatorLetters (π v)) (operatorLetters (compress E T)) J
    (operatorLetters_norm _ hπ) (operatorLetters_norm _ ((norm_compress_le E T).trans hT)) hθ hJ
  have hcost : (∑ w ∈ s, ‖σ (c w)‖ * w.length) ≤ wordTensorCost s c := by
    apply Finset.sum_le_sum
    intro w hw
    exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le σ _) (Nat.cast_nonneg _)
  apply hb.trans
  apply add_le_add
  · simpa only [hφ] using norm_model_amplifiedPolynomial_le_any s c φ K L π σ
  · exact mul_le_mul_of_nonneg_right hcost hθ

lemma norm_wordTensor_le_of_models_any (s : Finset (List Bool)) (c : List Bool → C)
    (v : B) (hv : ‖v‖ ≤ 1) (φ : UniversalContraction →⋆ₐ[ℂ] B)
    (hφ : φ universalContractionGenerator = v) {θ : ℝ} (hθ : 0 ≤ θ)
    (hmodels : FiniteContractionModelsAny B v θ) :
    ‖wordTensor s c‖ ≤ ‖minimalMapLeftAny φ.toNonUnitalStarAlgHom (wordTensor s c)‖ +
      wordTensorCost s c * θ := by
  let := CStarAlgebra.spectralOrder UniversalContraction
  let := CStarAlgebra.spectralOrderedRing UniversalContraction
  have hM : 0 ≤ ‖minimalMapLeftAny φ.toNonUnitalStarAlgHom (wordTensor s c)‖ +
      wordTensorCost s c * θ := add_nonneg (norm_nonneg _) (mul_nonneg (wordTensorCost_nonneg s c) hθ)
  change ‖(wordTensor s c).val‖ ≤ _
  rw [wordTensor_val]
  apply lp.norm_le_of_forall_le hM
  intro ρ
  rw [spatialSum_apply, norm_completion, norm_tensorSum_flip]
  apply (tensor_norm_le_faithful_finset s (fun w => ρ.rightRep (c w)) universalWord
    universalFaithfulRepresentation ρ.leftRep universalFaithfulRepresentation_injective).trans
  have he : ∀ w, universalFaithfulRepresentation (universalWord w) =
      wordEval (operatorLetters (universalUnitalRepresentation universalContractionGenerator)) w :=
    unitalRep_universalWord universalUnitalRepresentation
  simp only [he]
  exact norm_faithfulAmplifiedPolynomial_le_of_models_any s c v hv φ hφ hθ hmodels ρ.right ρ.rightRep

end

end WeakPureInfiniteness
end

end OAI
