import Mathlib
import OAI.Analysis.WeakInfiniteness.FaithfulRepresentation
import OAI.Analysis.WeakInfiniteness.NonunitalExactness

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

universe u

noncomputable section

variable {A B : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

theorem exact_subalgebra (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ)
    (hB : Exact B) : Exact A := by
  obtain ⟨H,π,hπ⟩ := exists_faithful_representation B
  exact exact_of_injective φ hφ H π hπ hB

lemma minimalMapLeft_injective {C : Type u} [NonUnitalCStarAlgebra C]
    (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ) :
    Function.Injective (minimalMapLeft (C := C) φ) := by
  obtain ⟨H,π,hπ⟩ := exists_faithful_representation B
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  apply norm_eq_zero.mp
  rw [← norm_minimalMapLeft φ H π hφ hπ z, hz, norm_zero]

end

end WeakPureInfiniteness
end

end OAI
