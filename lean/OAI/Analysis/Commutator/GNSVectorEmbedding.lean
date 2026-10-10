import Mathlib
import OAI.Analysis.Commutator.FiniteHankel
import OAI.Analysis.Commutator.TracialConjugation

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open UniformSpace ContinuousLinearMap

namespace Kadison.VectorGNS

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (τ : A →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hτ : ∀ a,τ a=inner ℂ ξ (φ a ξ))

def preMap : τ.PreGNS →ₗ[ℂ] H where
  toFun x := φ (τ.ofPreGNS x) ξ
  map_add' x y := by simp only [map_add,add_apply]
  map_smul' c x := by simp only [map_smul,smul_apply,RingHom.id_apply]

include hτ in
lemma inner_preMap (x y : τ.PreGNS) :
    inner ℂ (preMap τ φ ξ x) (preMap τ φ ξ y)=inner ℂ x y := by
  rw [PositiveLinearMap.preGNS_inner_def,hτ,map_mul,map_star]
  change inner ℂ (φ (τ.ofPreGNS x) ξ) (φ (τ.ofPreGNS y) ξ)=
    inner ℂ ξ ((φ (τ.ofPreGNS x)).adjoint (φ (τ.ofPreGNS y) ξ))
  exact (adjoint_inner_right _ _ _).symm

def preIsometry : τ.PreGNS →ₗᵢ[ℂ] H :=
  (preMap τ φ ξ).isometryOfInner (inner_preMap τ φ ξ hτ)

def embedding : τ.GNS →ₗᵢ[ℂ] H where
  toLinearMap := ((preIsometry τ φ ξ hτ).toContinuousLinearMap.extend
    (Completion.toComplL : τ.PreGNS →L[ℂ] τ.GNS)).toLinearMap
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x =>
      change ‖((preIsometry τ φ ξ hτ).toContinuousLinearMap.extend
        (Completion.toComplL : τ.PreGNS →L[ℂ] τ.GNS))
        ((Completion.toComplL : τ.PreGNS →L[ℂ] τ.GNS) x)‖=‖(x:τ.GNS)‖
      rw [extend_eq _ Completion.denseRange_coe (Completion.isUniformInducing_coe _),
        LinearIsometry.coe_toContinuousLinearMap,LinearIsometry.norm_map,Completion.norm_coe]

@[simp] lemma embedding_coe (a : A) :
    embedding τ φ ξ hτ (TracialGNS.algebraVector τ a)=φ a ξ := by
  change ((preIsometry τ φ ξ hτ).toContinuousLinearMap.extend
    (Completion.toComplL : τ.PreGNS →L[ℂ] τ.GNS))
    ((Completion.toComplL : τ.PreGNS →L[ℂ] τ.GNS) (τ.toPreGNS a))=_
  rw [extend_eq _ Completion.denseRange_coe (Completion.isUniformInducing_coe _)]
  rfl

lemma embedding_vacuum : embedding τ φ ξ hτ (TracialGNS.vacuum τ)=ξ := by
  change embedding τ φ ξ hτ (TracialGNS.algebraVector τ 1)=ξ
  rw [embedding_coe,map_one,one_apply_eq_self]

lemma intertwines (a : A) :
    (embedding τ φ ξ hτ).toContinuousLinearMap.comp (τ.gnsStarAlgHom a)=
      (φ a).comp (embedding τ φ ξ hτ).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  refine (TracialGNS.algebraVector_dense τ).induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  have hl : τ.gnsStarAlgHom a (TracialGNS.algebraVector τ b)=
      TracialGNS.algebraVector τ (a*b) := TracialGNS.left_coe τ a b
  simp only [comp_apply,LinearIsometry.coe_toContinuousLinearMap,hl,embedding_coe,
    map_mul,mul_apply_eq_comp]

lemma adjoint_intertwines (a : A) :
    (τ.gnsStarAlgHom a).comp (embedding τ φ ξ hτ).toContinuousLinearMap.adjoint=
      (embedding τ φ ξ hτ).toContinuousLinearMap.adjoint.comp (φ a) := by
  have he := congrArg (fun T : τ.GNS →L[ℂ] H => T.adjoint) (intertwines τ φ ξ hτ (star a))
  simpa only [adjoint_comp,map_star,star_eq_adjoint,adjoint_adjoint] using he

def compression (T : H →L[ℂ] H) : τ.GNS →L[ℂ] τ.GNS :=
  FreeCorner.compress (embedding τ φ ξ hτ) T

lemma compression_commutator (T : H →L[ℂ] H) (a : A) :
    compression τ φ ξ hτ T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*compression τ φ ξ hτ T=
      compression τ φ ξ hτ (T*φ a-φ a*T) := by
  simp only [compression,FreeCorner.compress,mul_def,comp_sub,sub_comp]
  congr 1
  · simp only [comp_assoc]
    rw [intertwines τ φ ξ hτ a]
  · simp only [←comp_assoc]
    rw [adjoint_intertwines τ φ ξ hτ a]

lemma norm_commutator_compression_le (T : H →L[ℂ] H) (a : A) :
    ‖compression τ φ ξ hτ T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*compression τ φ ξ hτ T‖≤
      ‖T*φ a-φ a*T‖ := by
  rw [compression_commutator]
  exact FreeCorner.norm_compress_le _ _

lemma compression_on_preserved (T : H →L[ℂ] H) (x y : τ.GNS)
    (hxy : T (embedding τ φ ξ hτ x)=embedding τ φ ξ hτ y) :
    compression τ φ ξ hτ T x=y := by
  change (embedding τ φ ξ hτ).toContinuousLinearMap.adjoint
    (T (embedding τ φ ξ hτ x))=y
  rw [hxy]
  have he := congrArg (fun B : τ.GNS →L[ℂ] τ.GNS => B y)
    (LinearIsometry.adjoint_comp_self (embedding τ φ ξ hτ))
  exact he

end Kadison.VectorGNS

end

end
end

end OAI
