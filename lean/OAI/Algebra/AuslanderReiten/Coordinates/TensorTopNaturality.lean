import OAI.Algebra.AuslanderReiten.Tensor.TwistedTensorResolution
import OAI.Algebra.AuslanderReiten.Coordinates.TensorTailTop

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Ae" => ExternalTensor.EnvelopingProduct k R R
local notation "D" => bimoduleTwoConeData q
local notation "Q" => sourceData q H

def bimoduleTopComparison (n : ℕ) : (Q).term n →ₗ[Ae] (D).term (n+1) :=
  ((ExternalTensor.envelopingFunctor k R R).map
    (ModuleCat.ofHom (tensorTopComparison q H n))).hom

def bimoduleEndpoint : (Q).term 0 →ₗ[Ae] (D).term 0 :=
  ((ExternalTensor.envelopingFunctor k R R).map
    (ModuleCat.ofHom (tensorEndpoint q H))).hom

theorem bimoduleTopComparison_chain (n : ℕ) :
    ((D).d (n+1)).comp (bimoduleTopComparison q H (n+1)) =
      (bimoduleTopComparison q H n).comp ((Q).d n) := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (tensorTopComparison_chain q H n) x

theorem bimoduleTopComparison_zero :
    ((D).d 0).comp (bimoduleTopComparison q H 0) = bimoduleEndpoint q H := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (tensorTopComparison_zero q H) x

def bimoduleTopCokernel (n : ℕ) : TwoCone.BaseCokernel Q n →ₗ[Ae]
    TwoCone.BaseCokernel D (n+1) :=
  (LinearMap.range ((Q).d n)).liftQ
    ((LinearMap.range ((D).d (n+1))).mkQ.comp (bimoduleTopComparison q H n)) (by
      rintro x ⟨y,rfl⟩
      change (LinearMap.range ((D).d (n+1))).mkQ
        (bimoduleTopComparison q H n ((Q).d n y)) = 0
      have h := LinearMap.congr_fun (bimoduleTopComparison_chain q H n) y
      change (D).d (n+1) (bimoduleTopComparison q H (n+1) y) =
        bimoduleTopComparison q H n ((Q).d n y) at h
      rw [← h]
      exact LinearMap.congr_fun (LinearMap.range_mkQ_comp ((D).d (n+1))) _)

@[simp] theorem bimoduleTopCokernel_mk (n : ℕ) (x : (Q).term n) :
    bimoduleTopCokernel q H n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (bimoduleTopComparison q H n x) := rfl

theorem bimoduleTopCokernel_four :
    (bimoduleTopCokernel q H 4).comp (sourceFourthEquiv q H).toLinearMap =
      topSyzygyMap q H := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

theorem bimoduleEndpoint_cycle : (bimoduleEndpoint q H).comp ((Q).d 0) = 0 := by
  rw [← bimoduleTopComparison_zero, LinearMap.comp_assoc,
    ← bimoduleTopComparison_chain, ← LinearMap.comp_assoc, (D).square 0, LinearMap.zero_comp]

def endpointOnCokernel : TwoCone.BaseCokernel Q 0 →ₗ[Ae] (D).term 0 :=
  (LinearMap.range ((Q).d 0)).liftQ (bimoduleEndpoint q H) (by
    rintro x ⟨y,rfl⟩
    exact LinearMap.congr_fun (bimoduleEndpoint_cycle q H) y)

@[simp] theorem endpointOnCokernel_mk (x : (Q).term 0) :
    endpointOnCokernel q H (Submodule.Quotient.mk x) = bimoduleEndpoint q H x := rfl

end ArExplicit.T

end

end OAI
