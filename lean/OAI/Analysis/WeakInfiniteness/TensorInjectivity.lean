import Mathlib
import OAI.Analysis.WeakInfiniteness.AlgebraicTensorSpan
import OAI.Analysis.WeakInfiniteness.TensorCompression
import OAI.Analysis.WeakInfiniteness.TensorFlip
import OAI.Analysis.WeakInfiniteness.TensorFunctoriality

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

namespace WeakPureInfiniteness

section TensorLeft

universe leftUniverse rightUniverse

variable {A B : Type leftUniverse} {C : Type rightUniverse}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

def SpatialRepresentation.precompLeft (π : SpatialRepresentation B C)
    (φ : A →⋆ₙₐ[ℂ] B) : SpatialRepresentation A C where
  left := π.left
  right := π.right
  leftRep := π.leftRep.comp φ
  rightRep := π.rightRep

def spatialMapLeft (φ : A →⋆ₙₐ[ℂ] B) : SpatialAmbient A C →⋆ₙₐ[ℂ] SpatialAmbient B C where
  toFun z := ⟨fun π => z (π.precompLeft φ), memℓp_infty ⟨‖z‖, by
    rintro _ ⟨π, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero z _⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp] lemma spatialMapLeft_elementary (φ : A →⋆ₙₐ[ℂ] B) (a : A) (c : C) :
    spatialMapLeft φ (spatialElementary a c) = spatialElementary (φ a) c := rfl

lemma spatialMapLeft_mem (φ : A →⋆ₙₐ[ℂ] B) {z : SpatialAmbient A C}
    (hz : z ∈ minimalTensorSubalgebra A C) :
    spatialMapLeft φ z ∈ minimalTensorSubalgebra B C := by
  apply NonUnitalStarSubalgebra.topologicalClosure_minimal _
    (t := NonUnitalStarSubalgebra.comap (spatialMapLeft φ) (minimalTensorSubalgebra B C))
    (NonUnitalStarAlgebra.adjoin_le ?_) ?_ hz
  · rintro _ ⟨⟨a,c⟩, rfl⟩
    change spatialMapLeft φ (spatialElementary a c) ∈ minimalTensorSubalgebra B C
    rw [spatialMapLeft_elementary]
    exact spatialElementary_mem (φ a) c
  · exact isClosed_closure.preimage (nonUnitalStarHom_continuous (spatialMapLeft φ))

def minimalMapLeft (φ : A →⋆ₙₐ[ℂ] B) : MinimalTensor A C →⋆ₙₐ[ℂ] MinimalTensor B C :=
  NonUnitalStarAlgHom.codRestrict
    ((spatialMapLeft φ).comp (NonUnitalStarSubalgebraClass.subtype (minimalTensorSubalgebra A C)))
    (minimalTensorSubalgebra B C) (fun z => spatialMapLeft_mem φ z.property)

@[simp] lemma minimalMapLeft_elementary (φ : A →⋆ₙₐ[ℂ] B) (a : A) (c : C) :
    minimalMapLeft φ (minimalElementary a c) = minimalElementary (φ a) c := rfl

lemma spatialSum_apply {ι : Type*} (s : Finset ι) (a : ι → A) (c : ι → C)
    (π : SpatialRepresentation A C) :
    (∑ i ∈ s, spatialElementary (a i) (c i)) π =
      (∑ i ∈ s, TensorProduct.mapL (π.leftRep (a i)) (π.rightRep (c i))).completion := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,completion_zero]; rfl
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi,completion_add]
    change _ + (∑ j ∈ s, spatialElementary (a j) (c j)) π = _
    rw [ih]
    rfl

lemma norm_spatialSum_le_image {ι : Type*} [Finite ι] (s : Finset ι)
    (a : ι → A) (c : ι → C) (φ : A →⋆ₙₐ[ℂ] B)
    (K : ComplexHilbert.{max leftUniverse rightUniverse}) (ψ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K))
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) :
    ‖∑ i ∈ s, spatialElementary (a i) (c i)‖ ≤
      ‖∑ i ∈ s, spatialElementary (φ (a i)) (c i)‖ := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro π
  rw [spatialSum_apply,norm_completion,norm_tensorSum_flip]
  apply (tensor_norm_le_faithful s (fun i => π.rightRep (c i)) a
    (ψ.comp φ) π.leftRep (hψ.comp hφ)).trans
  rw [norm_tensorSum_flip]
  let ρ : SpatialRepresentation B C :=
    { left := K, right := π.right, leftRep := ψ, rightRep := π.rightRep }
  have h := lp.norm_apply_le_norm ENNReal.top_ne_zero
    (∑ i ∈ s, spatialElementary (φ (a i)) (c i)) ρ
  change ‖(∑ i ∈ s, spatialElementary (φ (a i)) (c i)) ρ‖ ≤ _ at h
  rw [spatialSum_apply,norm_completion] at h
  exact h

lemma norm_spatialSum_le_image_finset {ι : Type*} (s : Finset ι)
    (a : ι → A) (c : ι → C) (φ : A →⋆ₙₐ[ℂ] B)
    (K : ComplexHilbert.{max leftUniverse rightUniverse}) (ψ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K))
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) :
    ‖∑ i ∈ s, spatialElementary (a i) (c i)‖ ≤
      ‖∑ i ∈ s, spatialElementary (φ (a i)) (c i)‖ := by
  classical
  rw [← Finset.sum_coe_sort s (fun i => spatialElementary (a i) (c i)),
    ← Finset.sum_coe_sort s (fun i => spatialElementary (φ (a i)) (c i))]
  exact norm_spatialSum_le_image Finset.univ (fun i : s => a i) (fun i : s => c i) φ K ψ hφ hψ

lemma norm_spatialMapLeft_ge_on_span
    (φ : A →⋆ₙₐ[ℂ] B) (K : ComplexHilbert.{max leftUniverse rightUniverse})
    (ψ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (z : SpatialAmbient A C)
    (hz : z ∈ Submodule.span ℂ (Set.range fun p : A × C => spatialElementary p.1 p.2)) :
    ‖z‖ ≤ ‖spatialMapLeft φ z‖ := by
  classical
  obtain ⟨d, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  simp only [Finsupp.sum, map_sum, map_smul, spatialMapLeft_elementary]
  simpa only [← spatialElementary_smul_left, map_smul] using
    norm_spatialSum_le_image_finset d.support (fun i => d i • i.1) Prod.snd φ K ψ hφ hψ

lemma norm_minimalMapLeft (φ : A →⋆ₙₐ[ℂ] B)
    (K : ComplexHilbert.{max leftUniverse rightUniverse})
    (ψ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (z : MinimalTensor A C) : ‖minimalMapLeft φ z‖ = ‖z‖ := by
  apply le_antisymm (NonUnitalStarAlgHom.norm_apply_le _ _)
  let S := {x : SpatialAmbient A C | ‖x‖ ≤ ‖spatialMapLeft φ x‖}
  have hc : IsClosed S := isClosed_le continuous_norm
    ((nonUnitalStarHom_continuous (spatialMapLeft φ)).norm)
  have hz := z.property
  change z.val ∈ (minimalTensorSubalgebra A C : Set (SpatialAmbient A C)) at hz
  rw [minimalTensor_eq_closure_span] at hz
  exact (closure_minimal (fun _ hx => norm_spatialMapLeft_ge_on_span φ K ψ hφ hψ _ hx) hc) hz

lemma minimalMapLeft_isometry (φ : A →⋆ₙₐ[ℂ] B)
    (K : ComplexHilbert.{max leftUniverse rightUniverse})
    (ψ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hφ : Function.Injective φ) (hψ : Function.Injective ψ) :
    Isometry (minimalMapLeft (C := C) φ) := by
  apply AddMonoidHomClass.isometry_of_norm
  exact norm_minimalMapLeft φ K ψ hφ hψ

end TensorLeft

end WeakPureInfiniteness
end

end OAI
