import Mathlib
import OAI.Analysis.WeakInfiniteness.FreeFiniteRepresentations
import OAI.Analysis.WeakInfiniteness.UniversalGroupNorm

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

lemma norm_fullToUniversal_polynomial (c : FreeGroup Bool →₀ ℂ) :
    ‖fullToUniversal (fullGroupPolynomial c)‖ = ‖fullGroupPolynomial c‖ := by
  apply le_antisymm (NonUnitalStarAlgHom.norm_apply_le fullToUniversal _)
  apply (norm_fullGroup_le_iff _ (norm_nonneg _)).mpr
  intro π
  rw [fullGroupEvaluation_polynomial]
  let ρ := Unitary.linearIsometryEquiv.toMonoidHom.comp π.group
  exact norm_freePolynomial_le_of_finite_tests c _ (norm_nonneg _)
    (fun V _ _ _ ρ => finite_norm_le_fullToUniversal c V ρ) ρ

lemma fullToUniversal_continuous : Continuous fullToUniversal :=
  (fullToUniversal.toAlgHom.toLinearMap.mkContinuous 1 (fun x => by
    change ‖fullToUniversal x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le fullToUniversal x)).continuous

lemma norm_fullToUniversal (x : FullGroupAlgebra (FreeGroup Bool)) :
    ‖fullToUniversal x‖ = ‖x‖ := by
  refine (fullGroupPolynomial_dense (G := FreeGroup Bool)).induction_on
    (p := fun y => ‖fullToUniversal y‖ = ‖y‖) x ?_ ?_
  · exact isClosed_eq (continuous_norm.comp fullToUniversal_continuous) continuous_norm
  · exact norm_fullToUniversal_polynomial

theorem fullToUniversal_isometry : Isometry fullToUniversal :=
  AddMonoidHomClass.isometry_of_norm fullToUniversal norm_fullToUniversal

lemma fullToUniversal_injective : Function.Injective fullToUniversal :=
  fullToUniversal_isometry.injective

end WeakPureInfiniteness
end

end OAI
