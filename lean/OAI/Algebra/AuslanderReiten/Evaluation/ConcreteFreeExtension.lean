import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteEndpointCoordinates
import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteBetaTransfer

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.T

private theorem fourTensor_ext {k R V W : Type*} [Field k]
    [AddCommGroup R] [Module k R] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (e : V ≃ₗ[k] ((R ⊗[k] R) ⊗[k] (R ⊗[k] R))) (f g : V →ₗ[k] W)
    (h : ∀ a b c d : R,
      f (e.symm ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d))) =
        g (e.symm ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d)))) : f = g := by
  have hh : f.comp e.symm.toLinearMap = g.comp e.symm.toLinearMap := by
    ext a b c d
    exact h a b c d
  ext v
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
    LinearMap.congr_fun hh (e v)

universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (hq1 : 1+q ≠ 0)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q
local notation "S" => Resolution.Simple q
local instance (priority := 3000) nativeSimpleScalar : Module k (A.simpleFiniteModule q).carrier :=
  (A.simpleFiniteModule q).scalar
local instance (priority := 3000) nativeSimpleTower : IsScalarTower k (A k q) (A.simpleFiniteModule q).carrier :=
  (A.simpleFiniteModule q).tower

def freeEndpointLinear (s t : S) : (D).term 0 →ₗ[k] A k q :=
  ((freeCoordinateRaw q hq1).restrictScalars k).comp
    (((BalancedTensor.mk (k := k) (R := A k q)
      (F := EnvelopingBimodule k (A k q) (TwoCone.termModule D hf 0).carrier)
      (M := (A.simpleFiniteModule q).carrier)).flip (s ⊗ₜ[k] t)).comp
        (EnvelopingBimodule.scalarEquiv (TwoCone.termModule D hf 0).carrier).symm.toLinearMap)

theorem freeCoordinateRaw_eq_endpointEvaluation
    (hPure : ∀ (a b c d : T k q) (s t : S),
      freeCoordinateRaw q hq1 (BalancedTensor.tmul
        (⟨(endpointCoordinates q).symm ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d))⟩ :
          EnvelopingBimodule k (A k q) (TwoCone.termModule D hf 0).carrier)
        (s ⊗ₜ[k] t)) =
      endpointEvaluation q s t
        ((endpointCoordinates q).symm ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d))))
    (z : (D).term 0) (s t : S) :
    freeCoordinateRaw q hq1 (BalancedTensor.tmul
      (⟨z⟩ : EnvelopingBimodule k (A k q) (TwoCone.termModule D hf 0).carrier)
      (s ⊗ₜ[k] t)) = endpointEvaluation q s t z := by
  have hh : freeEndpointLinear q hq1 s t = endpointEvaluation q s t :=
    fourTensor_ext (endpointCoordinates q) (freeEndpointLinear q hq1 s t)
      (endpointEvaluation q s t) (fun a b c d => hPure a b c d s t)
  exact LinearMap.congr_fun hh z

end ArExplicit.T

end

end OAI
