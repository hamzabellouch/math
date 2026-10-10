import OAI.Analysis.Nuclearity.NuclearCommutingRepresentation
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorLaws
import OAI.Analysis.Nuclearity.UnitalMinimalTensor

namespace OAI

/-! Unital forms of the nuclear commuting tensor representation and the
faithful inclusion of a right tensor factor. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder
namespace WeakPureInfiniteness

local instance unitalNuclearTensorStructure {B C : Type*} [CStarAlgebra B] [CStarAlgebra C] :
    CStarAlgebra (MinimalTensor B C) := minimalTensorUnitalStructure B C

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitalNuclearCommuting {C : Type*} [CStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] (hA : Nuclear A)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ a c, Commute (π a) (η c)) :
    MinimalTensor A C →⋆ₐ[ℂ] (H →L[ℂ] H) := by
  let f := nuclearCommutingRepresentation hA π.toNonUnitalStarAlgHom η hc
  have hf : f 1 = 1 := by
    rw [UnitalMinimalTensor.one_eq]
    change commutingMinimalLinear π.toNonUnitalStarAlgHom η (minimalElementary 1 1) = 1
    rw [commutingMinimalLinear_elementary hA _ _ hc]
    change π 1 * η 1 = 1
    rw [map_one, map_one, one_mul]
  exact { f with
    map_one' := hf
    commutes' := fun c => by
      change f (algebraMap ℂ (MinimalTensor A C) c) = algebraMap ℂ (H →L[ℂ] H) c
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hf, Algebra.algebraMap_eq_smul_one] }

def unitalTensorInclusion {C : Type*} [CStarAlgebra C]
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    MinimalTensor A C →⋆ₐ[ℂ] MinimalTensor A (H →L[ℂ] H) := by
  let j := minimalMapAny (NonUnitalStarAlgHom.id ℂ A) η.toNonUnitalStarAlgHom
  have hj : j 1 = 1 := by
    rw [UnitalMinimalTensor.one_eq, UnitalMinimalTensor.one_eq]
    change minimalMapAny _ _ (minimalElementary 1 1) = _
    rw [minimalMapAny_elementary]
    change minimalElementary (1 : A) (η 1) = _
    rw [map_one]
  exact { j with map_one' := hj
                 commutes' := fun c => by
                   change j (algebraMap ℂ (MinimalTensor A C) c) = _
                   rw [Algebra.algebraMap_eq_smul_one, map_smul, hj,
                     Algebra.algebraMap_eq_smul_one] }


lemma unitalNuclearCommuting_elementary {C : Type*} [CStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] (hA : Nuclear A)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ a c, Commute (π a) (η c)) (a : A) (c : C) :
    unitalNuclearCommuting hA π η hc (minimalElementary a c) = π a * η c :=
  commutingMinimalLinear_elementary hA π.toNonUnitalStarAlgHom η hc a c

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitalTensorInclusion_elementary {C : Type*} [CStarAlgebra C]
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) (c : C) :
    unitalTensorInclusion (A := A) η (minimalElementary a c) = minimalElementary a (η c) :=
  minimalMapAny_elementary _ _ a c

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitalTensorInclusion_injective {C : Type*} [CStarAlgebra C]
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hη : Function.Injective η) :
    Function.Injective (unitalTensorInclusion (A := A) η) :=
  (minimalMapAny_isometry (NonUnitalStarAlgHom.id ℂ A) η.toNonUnitalStarAlgHom
    Function.injective_id hη).injective

end WeakPureInfiniteness

end

end OAI
