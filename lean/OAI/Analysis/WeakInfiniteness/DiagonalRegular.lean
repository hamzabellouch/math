import Mathlib
import OAI.Analysis.WeakInfiniteness.ReducedGroupAlgebra
import OAI.Analysis.WeakInfiniteness.ScalarDiagonal

namespace OAI

universe u v

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace

namespace WeakPureInfiniteness

section ContinuousGroupCoefficients

variable {G : Type u} [Group G]

def starHomCLM {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) : A →L[ℂ] B :=
  φ.toAlgHom.toLinearMap.mkContinuous 1 (fun x => by
    change ‖φ x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ x)

@[simp] lemma starHomCLM_apply {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (x : A) : starHomCLM φ x = φ x := rfl

lemma groupCLM_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : FullGroupAlgebra G →L[ℂ] E)
    (h : ∀ s : G, f (fullGroupElement s) = g (fullGroupElement s)) : f = g := by
  apply DFunLike.coe_injective
  apply fullGroupPolynomial_dense.equalizer f.continuous g.continuous
  funext c
  simp only [Function.comp_apply, fullGroupPolynomial, Finsupp.linearCombination_apply,
    Finsupp.sum, map_sum, map_smul, h]

def rightGroupEvaluation : FullGroupAlgebra G →⋆ₐ[ℂ]
    (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  (groupInversion.conjStarAlgEquiv.toStarAlgHom).comp
    (fullGroupEvaluation (leftRegularRepresentation G))

lemma rightGroupEvaluation_element (s : G) :
    rightGroupEvaluation (fullGroupElement s) = rightRegular s := by
  apply ContinuousLinearMap.ext
  intro ξ
  change groupInversion ((leftRegular s : GroupHilbert G →L[ℂ] GroupHilbert G)
    (groupInversion.symm ξ)) = _
  rw [groupInversion_intertwines, LinearIsometryEquiv.apply_symm_apply]

lemma rightGroupEvaluation_eq_zero {b : FullGroupAlgebra G} (hb : fullToReduced b = 0) :
    rightGroupEvaluation b = 0 := by
  have h : fullGroupEvaluation (leftRegularRepresentation G) b = 0 :=
    congrArg Subtype.val hb
  change groupInversion.conjStarAlgEquiv
    (fullGroupEvaluation (leftRegularRepresentation G) b) = 0
  rw [h, map_zero]

end ContinuousGroupCoefficients

section MinimalElementaryContinuity

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def minimalElementaryLeft (b : B) : A →L[ℂ] MinimalTensor A B :=
  LinearMap.mkContinuous
    { toFun a := minimalElementary a b
      map_add' a a' := Subtype.ext (spatialElementary_add_left a a' b)
      map_smul' c a := Subtype.ext (spatialElementary_smul_left c a b) }
    ‖b‖ (fun a => by
      change ‖spatialElementary a b‖ ≤ ‖b‖ * ‖a‖
      simpa only [mul_comm ‖b‖] using norm_spatialElementary_le a b)

def minimalElementaryRight (a : A) : B →L[ℂ] MinimalTensor A B :=
  LinearMap.mkContinuous
    { toFun b := minimalElementary a b
      map_add' b b' := Subtype.ext (spatialElementary_add_right a b b')
      map_smul' c b := Subtype.ext (spatialElementary_smul_right c a b) }
    ‖a‖ (norm_spatialElementary_le a)

@[simp] lemma minimalElementaryLeft_apply (a : A) (b : B) :
    minimalElementaryLeft b a = minimalElementary a b := rfl

@[simp] lemma minimalElementaryRight_apply (a : A) (b : B) :
    minimalElementaryRight a b = minimalElementary a b := rfl

end MinimalElementaryContinuity

section RegularPairing

variable {G : Type u} [Group G]

abbrev regularBase : GroupHilbert G := by
  classical
  exact lp.single 2 1 1

lemma regularBase_eq [DecidableEq G] :
    regularBase (G := G) = lp.single 2 1 1 := by
  apply Subtype.ext
  funext g
  simp [regularBase, lp.single, Pi.single_apply]

def regularPairingRight (a : FullGroupAlgebra G) : FullGroupAlgebra G →L[ℂ] ℂ :=
  (innerSL ℂ (regularBase (G := G))).comp
    ((fullGroupEvaluation (leftRegularRepresentation G) a).comp
      ((ContinuousLinearMap.apply ℂ (GroupHilbert G) regularBase).comp
        (starHomCLM rightGroupEvaluation)))

def regularPairingLeft (b : FullGroupAlgebra G) : FullGroupAlgebra G →L[ℂ] ℂ :=
  (innerSL ℂ (regularBase (G := G))).comp
    ((ContinuousLinearMap.apply ℂ (GroupHilbert G) (rightGroupEvaluation b regularBase)).comp
      (starHomCLM (fullGroupEvaluation (leftRegularRepresentation G))))

lemma regularPairingRight_apply (a b : FullGroupAlgebra G) :
    regularPairingRight a b = inner ℂ (regularBase (G := G))
      (fullGroupEvaluation (leftRegularRepresentation G) a
        (rightGroupEvaluation b regularBase)) := rfl

lemma regularPairingLeft_apply (a b : FullGroupAlgebra G) :
    regularPairingLeft b a = regularPairingRight a b := rfl

end RegularPairing

section FreeRegularPairing

variable {α : Type u} [Fintype α] [DecidableEq α]

lemma freeDiagonalFunctional_regular (a b : FullGroupAlgebra (FreeGroup α)) :
    freeDiagonalFunctional (minimalElementary a b) = regularPairingRight a b := by
  classical
  have hright (s : FreeGroup α) :
      freeDiagonalFunctional.comp (minimalElementaryRight (fullGroupElement s)) =
        regularPairingRight (fullGroupElement s) := by
    apply groupCLM_ext
    intro t
    change freeDiagonalFunctional (minimalElementary (fullGroupElement s) (fullGroupElement t)) =
      regularPairingRight (fullGroupElement s) (fullGroupElement t)
    simp only [freeDiagonalFunctional_group_tensors, regularPairingRight_apply,
      rightGroupEvaluation_element]
    change (if s = t then (1 : ℂ) else 0) = inner ℂ (regularBase (G := FreeGroup α))
      ((leftRegular s : GroupHilbert (FreeGroup α) →L[ℂ] GroupHilbert (FreeGroup α))
        ((rightRegular t : GroupHilbert (FreeGroup α) →L[ℂ] GroupHilbert (FreeGroup α)) regularBase))
    rw [regularBase_eq]
    have hh := inner_leftRight_regular_base s t
    by_cases hst : s = t
    · simpa only [ite_eq_left hst, mul_apply_eq_comp] using hh.symm
    · simpa only [ite_eq_right hst, mul_apply_eq_comp] using hh.symm
  have hleft : freeDiagonalFunctional.comp (minimalElementaryLeft b) = regularPairingLeft b := by
    apply groupCLM_ext
    intro s
    exact DFunLike.congr_fun (hright s) b
  exact DFunLike.congr_fun hleft a

lemma freeDiagonalFunctional_elementary_kernel (a b : FullGroupAlgebra (FreeGroup α))
    (hb : fullToReduced b = 0) :
    freeDiagonalFunctional (minimalElementary a b) = 0 := by
  rw [freeDiagonalFunctional_regular, regularPairingRight_apply,
    rightGroupEvaluation_eq_zero hb]
  simp

end FreeRegularPairing

end WeakPureInfiniteness
end

end OAI
