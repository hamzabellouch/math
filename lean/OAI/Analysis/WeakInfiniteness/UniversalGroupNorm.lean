import Mathlib
import OAI.Analysis.WeakInfiniteness.GroupPolynomials
import OAI.Analysis.WeakInfiniteness.UniversalGroupMap

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

namespace WeakPureInfiniteness

lemma fullGroupEvaluation_polynomial {G : Type*} [Group G] (π : GroupRepresentation G)
    (c : G →₀ ℂ) : fullGroupEvaluation π (fullGroupPolynomial c) =
      c.sum (fun g a => a • (π.group g : π.hilbert →L[ℂ] π.hilbert)) := by
  simp only [fullGroupPolynomial, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, fullGroupEvaluation_element]

lemma finite_norm_le_fullToUniversal (c : FreeGroup Bool →₀ ℂ)
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : FreeGroup Bool →* V ≃ₗᵢ[ℂ] V) :
    ‖c.sum (fun g a => a • (ρ g : V →L[ℂ] V))‖ ≤ ‖fullToUniversal (fullGroupPolynomial c)‖ := by
  classical
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  cases subsingleton_or_nontrivial V with
  | inl h =>
    let := h
    have hz : c.sum (fun g a => a • (ρ g : V →L[ℂ] V)) = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero]
    exact norm_nonneg _
  | inr h =>
    let := h
    let uρ : FreeGroup Bool →* unitary (V →L[ℂ] V) :=
      Unitary.linearIsometryEquiv.symm.toMonoidHom.comp ρ
    let S := uρ (FreeGroup.of true)
    let T := uρ (FreeGroup.of false)
    let π : ContractionRepresentation :=
      { hilbert := ⟨V⟩
        operator := logarithmContraction S T
        norm_operator_le_one := norm_logarithmContraction_le S T }
    have hpair : pairGroup π.operator = uρ := by
      apply FreeGroup.ext_hom
      intro b
      rw [pairGroup_of]
      change pairUnitary (logarithmContraction S T) b = uρ (FreeGroup.of b)
      rw [pairUnitary_logarithmContraction]
      cases b <;> rfl
    have he : contractionEvaluation π (fullToUniversal (fullGroupPolynomial c)) =
        c.sum (fun g a => a • (ρ g : V →L[ℂ] V)) := by
      rw [fullToUniversal_evaluation,fullGroupEvaluation_polynomial]
      apply Finsupp.sum_congr
      intro g _
      change c g • (pairGroup π.operator g : V →L[ℂ] V) = c g • (ρ g : V →L[ℂ] V)
      rw [hpair]
      rfl
    exact he ▸ NonUnitalStarAlgHom.norm_apply_le (contractionEvaluation π)
      (fullToUniversal (fullGroupPolynomial c))

end WeakPureInfiniteness
end

end OAI
