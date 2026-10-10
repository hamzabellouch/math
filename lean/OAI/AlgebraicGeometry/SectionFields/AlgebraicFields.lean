import Mathlib
import OAI.AlgebraicGeometry.SectionFields.TensorAlgebra

namespace OAI

/-! Algebraic scalar extensions and finite Galois fields of definition. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators
open scoped TensorProduct
variable (K A L M : Type*) [Field K] [CommRing A] [Field L] [Field M]
  [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]

 

@[instance_reducible] noncomputable def tensorAlgebraicFractionField
    [IsDomain (A ⊗[K] L)] [IsFractionRing A M] [Algebra.IsAlgebraic K L] :
    Field (M ⊗[K] L) := by
  letI := tensorFraction_domain K A L M
  letI : Algebra.IsIntegral K L := (Algebra.isAlgebraic_iff_isIntegral).mp inferInstance
  exact (isField_of_isIntegral_of_isField' (R := M) (S := M ⊗[K] L)
    (Field.toIsField M)).toField

lemma tensorAlgebraicFraction_isFractionRing
    [IsDomain (A ⊗[K] L)] [IsFractionRing A M] [Algebra.IsAlgebraic K L] :
    letI := tensorFractionAlgebra K A L M
    IsFractionRing (A ⊗[K] L) (M ⊗[K] L) := by
  let := tensorFractionAlgebra K A L M
  let := tensorFraction_isLocalization K A L M
  let := tensorAlgebraicFractionField K A L M
  have hsub : Algebra.algebraMapSubmonoid (A ⊗[K] L) (nonZeroDivisors A) ≤
      nonZeroDivisors (A ⊗[K] L) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    have hn : Nontrivial A := (algebraMap A M).domain_nontrivial
    apply nonZeroDivisors.ne_zero ha
    apply Algebra.TensorProduct.includeLeft_injective (R := K) (S := K) (A := A) (B := L)
      (RingHom.injective (algebraMap K L))
    change a ⊗ₜ[K] (1 : L) = (0 : A) ⊗ₜ[K] (1 : L)
    change a ⊗ₜ[K] (1 : L) = 0 at h
    simpa only [TensorProduct.zero_tmul] using h
  have hinj : Function.Injective (algebraMap (A ⊗[K] L) (M ⊗[K] L)) :=
    IsLocalization.injective (M := Algebra.algebraMapSubmonoid (A ⊗[K] L)
      (nonZeroDivisors A)) _ hsub
  apply IsLocalization.of_le (Algebra.algebraMapSubmonoid (A ⊗[K] L)
    (nonZeroDivisors A)) (nonZeroDivisors (A ⊗[K] L)) hsub
  intro r hr
  exact isUnit_iff_ne_zero.mpr (fun hz => nonZeroDivisors.ne_zero hr
    (hinj (hz.trans (map_zero _).symm)))

end RelativeDenominators

open scoped TensorProduct

namespace RelativeDenominators
section

 
def tensorIntermediateInclusion
    (K A L : Type*) [Field K] [CommRing A] [Field L] [Algebra K A] [Algebra K L]
    (E : IntermediateField K L) : A ⊗[K] E →ₐ[K] A ⊗[K] L :=
  Algebra.TensorProduct.map (AlgHom.id K A) E.val

lemma tensorIntermediateInclusion_transition
    (K A L : Type*) [Field K] [CommRing A] [Field L] [Algebra K A] [Algebra K L]
    {E F : IntermediateField K L} (h : E ≤ F) (x : A ⊗[K] E) :
    tensorIntermediateInclusion K A L F
      (Algebra.TensorProduct.map (AlgHom.id K A) (IntermediateField.inclusion h) x) =
    tensorIntermediateInclusion K A L E x := by
  induction x using TensorProduct.inductionOn with
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

 

theorem tensor_finiteGalois_field_of_definition
    (K A L : Type*) [Field K] [CommRing A] [Field L] [Algebra K A] [Algebra K L]
    [IsGalois K L] (x : A ⊗[K] L) :
    ∃ (E : FiniteGaloisIntermediateField K L) (y : A ⊗[K] E),
      tensorIntermediateInclusion K A L E.toIntermediateField y = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a l =>
      let E := FiniteGaloisIntermediateField.adjoin K ({l} : Set L)
      have hl : l ∈ E.toIntermediateField :=
        FiniteGaloisIntermediateField.subset_adjoin K _ (Set.mem_singleton l)
      exact ⟨E, a ⊗ₜ[K] (⟨l, hl⟩ : E), rfl⟩
  | add x y hx hy =>
      obtain ⟨E, x', hx'⟩ := hx
      obtain ⟨F, y', hy'⟩ := hy
      let G := E ⊔ F
      have hE : E.toIntermediateField ≤ G.toIntermediateField := le_sup_left
      have hF : F.toIntermediateField ≤ G.toIntermediateField := le_sup_right
      refine ⟨G, Algebra.TensorProduct.map (AlgHom.id K A)
          (IntermediateField.inclusion hE) x' +
        Algebra.TensorProduct.map (AlgHom.id K A)
          (IntermediateField.inclusion hF) y', ?_⟩
      rw [map_add, tensorIntermediateInclusion_transition,
        tensorIntermediateInclusion_transition, hx', hy']

open scoped TensorProduct

lemma tensorIntermediateInclusion_injective
    (K A L : Type*) [Field K] [CommRing A] [Field L] [Algebra K A] [Algebra K L]
    (E : IntermediateField K L) :
    Function.Injective (tensorIntermediateInclusion K A L E) := by
  change Function.Injective (LinearMap.lTensor A E.val.toLinearMap)
  exact Module.Flat.lTensor_preserves_injective_linearMap E.val.toLinearMap E.val.injective

lemma tensorIntermediate_domain
    (K A L : Type*) [Field K] [CommRing A] [Field L] [Algebra K A] [Algebra K L]
    [IsDomain (A ⊗[K] L)] (E : IntermediateField K L) : IsDomain (A ⊗[K] E) :=
  (tensorIntermediateInclusion_injective K A L E).isDomain
    (tensorIntermediateInclusion K A L E).toRingHom

 

def tensorIntermediateInclusionOver
    (K A L M : Type*) [Field K] [CommRing A] [Field L] [CommRing M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    (E : IntermediateField K L) : M ⊗[K] E →ₐ[A] M ⊗[K] L where
  __ := (tensorIntermediateInclusion K M L E).toRingHom
  commutes' a := by
    change Algebra.TensorProduct.map (AlgHom.id K M) E.val
      (algebraMap A M a ⊗ₜ[K] (1 : E)) = algebraMap A M a ⊗ₜ[K] (1 : L)
    simp

end

open scoped TensorProduct

 

theorem tensor_isIntegrallyClosed_of_algebraic_galois
    (K A L M : Type*) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [IsIntegrallyClosed A] [IsGalois K L]
    [IsDomain (A ⊗[K] L)] : IsIntegrallyClosed (A ⊗[K] L) := by
  let := tensorFractionAlgebra K A L M
  let := tensorFraction_isScalarTower K A L M
  let := tensorAlgebraicFraction_isFractionRing K A L M
  let := tensorAlgebraicFractionField K A L M
  apply (isIntegrallyClosed_iff (M ⊗[K] L)).mpr
  intro x hx
  have hxA : IsIntegral A x := isIntegral_trans x hx
  obtain ⟨E, y, hy⟩ := tensor_finiteGalois_field_of_definition K M L x
  let := tensorIntermediate_domain K A L E.toIntermediateField
  let := tensorFractionAlgebra K A E M
  let := tensorFraction_isScalarTower K A E M
  let := tensorFraction_isFractionRing K A E M
  let := tensorFractionField K A E M
  let := tensor_isIntegrallyClosed_of_galois K A E M
  have hiy : IsIntegral A y := by
    apply (isIntegral_algHom_iff (tensorIntermediateInclusionOver K A L M E.toIntermediateField)
      (tensorIntermediateInclusion_injective K M L E.toIntermediateField)).mp
    change IsIntegral A (tensorIntermediateInclusion K M L E.toIntermediateField y)
    rw [hy]
    exact hxA
  obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff (M ⊗[K] E)).mp
    (inferInstance : IsIntegrallyClosed (A ⊗[K] E)) hiy.tower_top
  refine ⟨tensorIntermediateInclusion K A L E.toIntermediateField a, ?_⟩
  rw [← hy, ← ha]
  change Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A M) (AlgHom.id K L)
      (tensorIntermediateInclusion K A L E.toIntermediateField a) =
    tensorIntermediateInclusion K M L E.toIntermediateField
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A M) (AlgHom.id K E) a)
  clear ha
  induction a using TensorProduct.inductionOn with
  | tmul a e => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

end RelativeDenominators

end

end OAI
