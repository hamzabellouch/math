import Mathlib
import OAI.Analysis.WeakInfiniteness.NonUnitalClosedRange
import OAI.Analysis.WeakInfiniteness.TensorFoundations

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

universe u v

section TensorFunctoriality

variable {A : Type u} {C D : Type v}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def spatialMapRight (q : C →⋆ₙₐ[ℂ] D) : SpatialAmbient A C →⋆ₙₐ[ℂ] SpatialAmbient A D where
  toFun z := ⟨fun π => z (π.precompRight q), memℓp_infty ⟨‖z‖, by
    rintro _ ⟨π, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero z (π.precompRight q)⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp]
lemma spatialMapRight_elementary (q : C →⋆ₙₐ[ℂ] D) (a : A) (c : C) :
    spatialMapRight q (spatialElementary a c) = spatialElementary a (q c) := rfl

lemma spatialElementary_mem (a : A) (c : C) :
    spatialElementary a c ∈ minimalTensorSubalgebra A C :=
  NonUnitalStarSubalgebra.le_topologicalClosure _
    (NonUnitalStarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self (a,c)))

def minimalElementary (a : A) (c : C) : MinimalTensor A C :=
  ⟨spatialElementary a c, spatialElementary_mem a c⟩

lemma spatialMapRight_mem (q : C →⋆ₙₐ[ℂ] D) {z : SpatialAmbient A C}
    (hz : z ∈ minimalTensorSubalgebra A C) :
    spatialMapRight q z ∈ minimalTensorSubalgebra A D := by
  apply NonUnitalStarSubalgebra.topologicalClosure_minimal _
    (t := NonUnitalStarSubalgebra.comap (spatialMapRight q) (minimalTensorSubalgebra A D))
    (NonUnitalStarAlgebra.adjoin_le ?_) ?_ hz
  · rintro _ ⟨⟨a,c⟩, rfl⟩
    change spatialMapRight q (spatialElementary a c) ∈ minimalTensorSubalgebra A D
    rw [spatialMapRight_elementary]
    exact spatialElementary_mem a (q c)
  · exact isClosed_closure.preimage (nonUnitalStarHom_continuous (spatialMapRight q))

def minimalMapRight (q : C →⋆ₙₐ[ℂ] D) : MinimalTensor A C →⋆ₙₐ[ℂ] MinimalTensor A D :=
  NonUnitalStarAlgHom.codRestrict
    ((spatialMapRight q).comp (NonUnitalStarSubalgebraClass.subtype (minimalTensorSubalgebra A C)))
    (minimalTensorSubalgebra A D) (fun z => spatialMapRight_mem q z.property)

@[simp]
lemma minimalMapRight_elementary (q : C →⋆ₙₐ[ℂ] D) (a : A) (c : C) :
    minimalMapRight q (minimalElementary a c) = minimalElementary a (q c) := rfl

theorem minimalMapRight_surjective (q : C →⋆ₙₐ[ℂ] D) (hq : Function.Surjective q) :
    Function.Surjective (minimalMapRight (A := A) q) := by
  let F := (NonUnitalStarSubalgebraClass.subtype (minimalTensorSubalgebra A D)).comp
    (minimalMapRight (A := A) q)
  have hle : minimalTensorSubalgebra A D ≤ NonUnitalStarAlgHom.range F := by
    apply NonUnitalStarSubalgebra.topologicalClosure_minimal _
      (NonUnitalStarAlgebra.adjoin_le ?_)
    · exact nonUnitalStarHom_isClosed_range F
    · rintro _ ⟨⟨a,d⟩, rfl⟩
      obtain ⟨c, rfl⟩ := hq d
      exact ⟨minimalElementary a c, rfl⟩
  intro z
  obtain ⟨y, hy⟩ := hle z.property
  exact ⟨y, Subtype.ext hy⟩

end TensorFunctoriality

end WeakPureInfiniteness
end

end OAI
