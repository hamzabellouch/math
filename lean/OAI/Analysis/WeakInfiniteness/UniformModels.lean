import Mathlib
import OAI.Analysis.WeakInfiniteness.FaithfulContractions
import OAI.Analysis.WeakInfiniteness.UniversalMapping

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

def FiniteContractionModels (B : Type 1) [CStarAlgebra B] (v : B) (θ : ℝ) : Prop :=
  ∀ (H : ComplexHilbert.{1}) [FiniteDimensional ℂ H] (D : H →L[ℂ] H), ‖D‖ ≤ 1 →
    ∃ K : ComplexHilbert.{1}, ∃ π : B →⋆ₐ[ℂ] (K →L[ℂ] K), ∃ J : H →ₗᵢ[ℂ] K,
      ‖(π v).comp J.toContinuousLinearMap - J.toContinuousLinearMap.comp D‖ ≤ θ ∧
      ‖(star (π v)).comp J.toContinuousLinearMap - J.toContinuousLinearMap.comp (star D)‖ ≤ θ

lemma universalFaithfulRepresentation_one : universalFaithfulRepresentation 1 = 1 := by
  ext ξ
  rfl

def universalUnitalRepresentation :
    UniversalContraction →⋆ₐ[ℂ] (universalHilbert →L[ℂ] universalHilbert) :=
  { universalFaithfulRepresentation with
    map_one' := universalFaithfulRepresentation_one
    commutes' := fun c => by
      change universalFaithfulRepresentation (c • 1) = c • 1
      rw [map_smul, universalFaithfulRepresentation_one] }

lemma unitalRep_universalWord {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UniversalContraction →⋆ₐ[ℂ] (H →L[ℂ] H)) (w : List Bool) :
    π (universalWord w) = wordEval (operatorLetters (π universalContractionGenerator)) w := by
  rw [← algebraWord_universal, map_algebraWord, algebraWord_operator]

lemma operatorLetters_norm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ∀ i, ‖operatorLetters T i‖ ≤ 1 := by
  intro i
  cases i <;> simpa [operatorLetters] using hT

lemma tensor_norm_le_faithful_finset {H K L A ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (s : Finset ι) (T : ι → H →L[ℂ] H) (a : ι → A)
    (φ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (ψ : A →⋆ₙₐ[ℂ] (L →L[ℂ] L))
    (hφ : Function.Injective φ) :
    ‖∑ i ∈ s, TensorProduct.mapL (T i) (ψ (a i))‖ ≤
      ‖∑ i ∈ s, TensorProduct.mapL (T i) (φ (a i))‖ := by
  classical
  rw [← Finset.sum_coe_sort s (fun i => TensorProduct.mapL (T i) (ψ (a i))),
    ← Finset.sum_coe_sort s (fun i => TensorProduct.mapL (T i) (φ (a i)))]
  exact tensor_norm_le_faithful Finset.univ (fun i : s => T i) (fun i : s => a i) φ ψ hφ

section PolynomialTensorEstimate

variable {B C : Type 1} [CStarAlgebra B] [NonUnitalCStarAlgebra C]

def wordTensor (s : Finset (List Bool)) (c : List Bool → C) : MinimalTensor UniversalContraction C :=
  ∑ w ∈ s, minimalElementary (universalWord w) (c w)

lemma wordTensor_val (s : Finset (List Bool)) (c : List Bool → C) :
    (wordTensor s c).val = ∑ w ∈ s, spatialElementary (universalWord w) (c w) := by
  change (minimalTensorSubalgebra UniversalContraction C).subtype
    (∑ w ∈ s, minimalElementary (universalWord w) (c w)) = _
  rw [map_sum]
  rfl

lemma minimalMapLeft_wordTensor (s : Finset (List Bool)) (c : List Bool → C)
    (φ : UniversalContraction →⋆ₐ[ℂ] B) :
    minimalMapLeft φ.toNonUnitalStarAlgHom (wordTensor s c) =
      ∑ w ∈ s, minimalElementary (φ (universalWord w)) (c w) := by
  rw [wordTensor, map_sum]
  apply Finset.sum_congr rfl
  intro w _hw
  exact minimalMapLeft_elementary φ.toNonUnitalStarAlgHom (universalWord w) (c w)

def wordTensorCost (s : Finset (List Bool)) (c : List Bool → C) : ℝ :=
  ∑ w ∈ s, ‖c w‖ * w.length

lemma wordTensorCost_nonneg (s : Finset (List Bool)) (c : List Bool → C) :
    0 ≤ wordTensorCost s c := by
  unfold wordTensorCost
  positivity

lemma norm_model_amplifiedPolynomial_le (s : Finset (List Bool)) (c : List Bool → C)
    (φ : UniversalContraction →⋆ₐ[ℂ] B) (K L : ComplexHilbert.{1})
    (π : B →⋆ₐ[ℂ] (L →L[ℂ] L)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖amplifiedPolynomial s (fun w => σ (c w))
      (operatorLetters (π (φ universalContractionGenerator)))‖ ≤
      ‖minimalMapLeft φ.toNonUnitalStarAlgHom (wordTensor s c)‖ := by
  let ρ : SpatialRepresentation B C :=
    { left := L, right := K, leftRep := π.toNonUnitalStarAlgHom, rightRep := σ }
  calc
    _ = ‖∑ w ∈ s, TensorProduct.mapL (π (φ (universalWord w))) (σ (c w))‖ := by
      rw [norm_tensorSum_flip]
      unfold amplifiedPolynomial
      congr 1
      apply Finset.sum_congr rfl
      intro w _hw
      congr 1
      exact (unitalRep_universalWord (π.comp φ) w).symm
    _ = ‖((minimalMapLeft φ.toNonUnitalStarAlgHom (wordTensor s c)).val) ρ‖ := by
      rw [minimalMapLeft_wordTensor]
      change _ = ‖((minimalTensorSubalgebra B C).subtype
        (∑ w ∈ s, minimalElementary (φ (universalWord w)) (c w))) ρ‖
      rw [map_sum]
      change _ = ‖(∑ w ∈ s, spatialElementary (φ (universalWord w)) (c w)) ρ‖
      rw [spatialSum_apply, norm_completion]
      rfl
    _ ≤ _ := lp.norm_apply_le_norm ENNReal.top_ne_zero _ ρ

lemma norm_faithfulAmplifiedPolynomial_le_of_models (s : Finset (List Bool)) (c : List Bool → C)
    (v : B) (hv : ‖v‖ ≤ 1) (φ : UniversalContraction →⋆ₐ[ℂ] B)
    (hφ : φ universalContractionGenerator = v) {θ : ℝ} (hθ : 0 ≤ θ)
    (hmodels : FiniteContractionModels B v θ) (K : ComplexHilbert.{1})
    (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖amplifiedPolynomial s (fun w => σ (c w))
      (operatorLetters (universalUnitalRepresentation universalContractionGenerator))‖ ≤
      ‖minimalMapLeft φ.toNonUnitalStarAlgHom (wordTensor s c)‖ + wordTensorCost s c * θ := by
  have hM : 0 ≤ ‖minimalMapLeft φ.toNonUnitalStarAlgHom (wordTensor s c)‖ +
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
  · simpa only [hφ] using norm_model_amplifiedPolynomial_le s c φ K L π σ
  · exact mul_le_mul_of_nonneg_right hcost hθ

lemma norm_wordTensor_le_of_models (s : Finset (List Bool)) (c : List Bool → C)
    (v : B) (hv : ‖v‖ ≤ 1) (φ : UniversalContraction →⋆ₐ[ℂ] B)
    (hφ : φ universalContractionGenerator = v) {θ : ℝ} (hθ : 0 ≤ θ)
    (hmodels : FiniteContractionModels B v θ) :
    ‖wordTensor s c‖ ≤ ‖minimalMapLeft φ.toNonUnitalStarAlgHom (wordTensor s c)‖ +
      wordTensorCost s c * θ := by
  let := CStarAlgebra.spectralOrder UniversalContraction
  let := CStarAlgebra.spectralOrderedRing UniversalContraction
  have hM : 0 ≤ ‖minimalMapLeft φ.toNonUnitalStarAlgHom (wordTensor s c)‖ +
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
  exact norm_faithfulAmplifiedPolynomial_le_of_models s c v hv φ hφ hθ hmodels ρ.right ρ.rightRep

end PolynomialTensorEstimate

end

end WeakPureInfiniteness
end

end OAI
