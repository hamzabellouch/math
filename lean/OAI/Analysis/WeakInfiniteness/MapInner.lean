import Mathlib
import OAI.Analysis.WeakInfiniteness.UnitaryIntertwining

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

universe u v w

variable {B : Type u} {C : Type v} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

def mapUnitary (φ : B →⋆ₙₐ[ℂ] C) (u : unitary (Unitization ℂ B)) :
    unitary (Unitization ℂ C) :=
  ⟨Unitization.starMap φ u,by
    exact Unitary.map_mem (Unitization.starMap φ) u.property⟩

lemma map_unitizationInnerFun (φ : B →⋆ₙₐ[ℂ] C)
    (u : unitary (Unitization ℂ B)) (b : B) :
    φ (unitizationInnerFun u b)=unitizationInnerFun (mapUnitary φ u) (φ b) := by
  apply Unitization.inr_injective (R := ℂ)
  rw [inr_unitizationInnerFun]
  rw [← Unitization.starMap_inr]
  rw [inr_unitizationInnerFun]
  simp only [Unitary.conjStarAlgAut_apply,map_mul,map_star,mapUnitary]
  rw [Unitization.starMap_inr]

end

end WeakPureInfiniteness
end

end OAI
