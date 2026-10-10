import Mathlib

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

open scoped CStarAlgebra

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma map_posPart (π : A →⋆ₙₐ[ℂ] B) {a : A} (ha : IsSelfAdjoint a) : π a⁺=(π a)⁺ := by
  rw [CFC.posPart_def,CFC.posPart_def]
  exact π.map_cfcₙ (·⁺ : ℝ → ℝ) a (by fun_prop) (by simp) (by fun_prop) ha (ha.map π)

lemma map_negPart (π : A →⋆ₙₐ[ℂ] B) {a : A} (ha : IsSelfAdjoint a) : π a⁻=(π a)⁻ := by
  rw [CFC.negPart_def,CFC.negPart_def]
  exact π.map_cfcₙ (·⁻ : ℝ → ℝ) a (by fun_prop) (by simp) (by fun_prop) ha (ha.map π)

end

end WeakPureInfiniteness
end

end OAI
