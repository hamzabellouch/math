import Mathlib
import OAI.Analysis.Commutator.HilbertDiagonal
import OAI.Analysis.Commutator.InvariantSum

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
open scoped InnerProductSpace ENNReal
open scoped ComplexOrder InnerProductSpace TensorProduct
open UniformSpace ContinuousLinearMap
open scoped ComplexOrder InnerProductSpace TensorProduct
open UniformSpace ContinuousLinearMap

namespace Kadison.TracialGNS

open PreHilbert HilbertTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

variable (J : ℕ → Type*) [∀ k, NormedAddCommGroup (J k)]
  [∀ k, InnerProductSpace ℂ (J k)]

def sumConjugationIso (u : unitary A) (k : ℕ) : sumLevel τ J k →ₗᵢ[ℂ] sumLevel τ J k :=
  completionIsometry (TensorProduct.mapIsometry (wordConjugation τ hτ u k) LinearIsometry.id)

lemma sumConjugationIso_pair (u : unitary A) (k : ℕ)
    (x : wordSpace (fullSpace τ) (zeroSpace τ) k) (a : J k) :
    sumConjugationIso τ hτ J u k (pair x a)=pair (wordConjugation τ hτ u k x) a := by
  exact completionIsometry_coe
    (TensorProduct.mapIsometry (wordConjugation τ hτ u k) LinearIsometry.id) (x ⊗ₜ[ℂ] a)

lemma sumConjugationIso_toCLM (u : unitary A) (k : ℕ) :
    (sumConjugationIso τ hτ J u k).toContinuousLinearMap=sumConjugation τ hτ J u k := by
  apply completion_ext
  intro x a
  change sumConjugationIso τ hτ J u k (pair x a)=
    HilbertTensor.map (wordConjugation τ hτ u k).toContinuousLinearMap 1 (pair x a)
  rw [sumConjugationIso_pair,map_pair]
  rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : ∀ k, sumLevel τ J k →ₗᵢ[ℂ] H) (hU : IsHilbertSum ℂ (sumLevel τ J) U)

def freeConjugation (u : unitary A) : H →ₗᵢ[ℂ] H :=
  HilbertDiagonal.onSum (sumLevel τ J) U hU (sumConjugationIso τ hτ J u)

lemma freeConjugation_comp (u : unitary A) (k : ℕ) :
    (freeConjugation τ hτ J U hU u).toContinuousLinearMap.comp (U k).toContinuousLinearMap =
      (U k).toContinuousLinearMap.comp (sumConjugation τ hτ J u k) := by
  unfold freeConjugation
  rw [HilbertDiagonal.onSum_comp, sumConjugationIso_toCLM]

lemma conjugation_one : conjugation τ hτ 1 = LinearIsometry.id := by
  apply LinearIsometry.ext
  have h := (algebraVector_dense τ).equalizer (conjugation τ hτ 1).continuous
    (LinearIsometry.id (R:=ℂ) (E:=τ.GNS)).continuous (by
      funext a
      simp only [Function.comp_apply,algebraVector_apply,conjugation_coe,OneMemClass.coe_one,
        one_mul,star_one,mul_one,LinearIsometry.id_apply])
  exact congrFun h

lemma conjugation_mul (u v : unitary A) :
    conjugation τ hτ (u*v)=(conjugation τ hτ u).comp (conjugation τ hτ v) := by
  apply LinearIsometry.ext
  have h := (algebraVector_dense τ).equalizer (conjugation τ hτ (u*v)).continuous
    ((conjugation τ hτ u).comp (conjugation τ hτ v)).continuous (by
      funext a
      change conjugation τ hτ (u*v) (τ.toPreGNS a : τ.GNS)=
        conjugation τ hτ u (conjugation τ hτ v (τ.toPreGNS a : τ.GNS))
      simp only [conjugation_coe,Submonoid.coe_mul,star_mul,mul_assoc])
  exact congrFun h

lemma wordConjugation_one (k : ℕ) : wordConjugation τ hτ 1 k=LinearIsometry.id := by
  apply LinearIsometry.toContinuousLinearMap_injective
  apply continuousLinearMap_ext_word
  intro d x
  simp only [LinearIsometry.coe_toContinuousLinearMap,wordConjugation,wordMap_word,
    conjugation_one,LinearIsometry.id_apply]
  rfl

lemma wordConjugation_mul (u v : unitary A) (k : ℕ) :
    wordConjugation τ hτ (u*v) k=(wordConjugation τ hτ u k).comp
      (wordConjugation τ hτ v k) := by
  apply LinearIsometry.toContinuousLinearMap_injective
  apply continuousLinearMap_ext_word
  intro d x
  simp only [LinearIsometry.coe_toContinuousLinearMap,LinearIsometry.coe_comp,
    Function.comp_apply,wordConjugation,wordMap_word,conjugation_mul]
  rfl

lemma sumConjugationIso_one (k : ℕ) : sumConjugationIso τ hτ J 1 k=LinearIsometry.id := by
  apply LinearIsometry.toContinuousLinearMap_injective
  apply HilbertTensor.completion_ext
  intro a b
  change sumConjugationIso τ hτ J 1 k (pair a b)=pair a b
  rw [sumConjugationIso_pair,wordConjugation_one,LinearIsometry.id_apply]

lemma sumConjugationIso_mul (u v : unitary A) (k : ℕ) :
    sumConjugationIso τ hτ J (u*v) k=(sumConjugationIso τ hτ J u k).comp
      (sumConjugationIso τ hτ J v k) := by
  apply LinearIsometry.toContinuousLinearMap_injective
  apply HilbertTensor.completion_ext
  intro a b
  change sumConjugationIso τ hτ J (u*v) k (pair a b)=
    sumConjugationIso τ hτ J u k (sumConjugationIso τ hτ J v k (pair a b))
  rw [sumConjugationIso_pair,sumConjugationIso_pair,sumConjugationIso_pair,wordConjugation_mul]
  rfl

lemma freeConjugation_one : freeConjugation τ hτ J U hU 1=LinearIsometry.id := by
  unfold freeConjugation
  have h : sumConjugationIso τ hτ J 1=fun _ => LinearIsometry.id :=
    funext (sumConjugationIso_one τ hτ J)
  rw [h]
  exact HilbertDiagonal.onSum_one (sumLevel τ J) U hU

lemma freeConjugation_mul (u v : unitary A) :
    freeConjugation τ hτ J U hU (u*v)=(freeConjugation τ hτ J U hU u).comp
      (freeConjugation τ hτ J U hU v) := by
  unfold freeConjugation
  rw [HilbertDiagonal.onSum_mul]
  congr 1
  funext k
  exact sumConjugationIso_mul τ hτ J u v k

lemma freeConjugation_star_left (u : unitary A) :
    (freeConjugation τ hτ J U hU (star u)).comp (freeConjugation τ hτ J U hU u)=LinearIsometry.id := by
  rw [←freeConjugation_mul,Unitary.star_mul_self,freeConjugation_one]

lemma freeConjugation_surjective (u : unitary A) :
    Function.Surjective (freeConjugation τ hτ J U hU u) := by
  intro x
  refine ⟨freeConjugation τ hτ J U hU (star u) x,?_⟩
  have h := congrArg (fun V : H →ₗᵢ[ℂ] H => V x)
    (freeConjugation_star_left τ hτ J U hU (star u))
  change freeConjugation τ hτ J U hU (star (star u))
    (freeConjugation τ hτ J U hU (star u) x)=x at h
  simpa only [star_star] using h

end Kadison.TracialGNS
end

end OAI
