import OAI.Algebra.AuslanderReiten.Modules.ATwistFunctor
import OAI.Algebra.AuslanderReiten.Tensor.TwistedEnvelopingEndpoint
import OAI.Algebra.AuslanderReiten.Ext.ExactFunctorExtIso
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorFunctorExt
import OAI.Algebra.AuslanderReiten.Modules.TwistedFiniteEndpoint

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

abbrev evaluatedTwistFunctor := BalancedTensor.functor (k := k) (R := A k q) (S := A k q)
  (F := EnvelopingBimodule k (A k q) (twistedFiniteModule (sourceTwist q H)).carrier)

def evaluatedTwistIso :=
  BalancedTensor.nativeEvaluationIso
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)

omit [CharP k 2] [HasDerivedCategory (ModuleCat (T k q))] in
theorem evaluatedTwistIso_tmul
    (a : EnvelopingBimodule k (A k q) (twistedFiniteModule (sourceTwist q H)).carrier)
    (x : A.Simple q) :
    type_of% ((BalancedTensor.nativeEvaluationIso_tmul
      (A.simpleFiniteModule q) (evaluatedTwistEquiv q H) a x).trans
        (evaluatedTwistEquiv_tmul q H a x)) :=
  (BalancedTensor.nativeEvaluationIso_tmul
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H) a x).trans
      (evaluatedTwistEquiv_tmul q H a x)

omit [CharP k 2] [HasDerivedCategory (ModuleCat (T k q))] in
theorem inverseEndpoint_inv_apply (x : (Resolution.aInverseRestriction q H).obj (A.Simple q)) :
    (Resolution.aInverseEndpoint q H).inv.hom x = x := by
  have hh := congrArg (fun f => f.hom x) (Resolution.aInverseEndpoint q H).inv_hom_id
  change (Resolution.aInverseEndpoint q H).hom.hom
    ((Resolution.aInverseEndpoint q H).inv.hom x) = x at hh
  rw [Resolution.aInverseEndpoint_apply] at hh
  exact hh

omit [CharP k 2] [HasDerivedCategory (ModuleCat (T k q))] in
theorem evaluatedRestriction_tmul
    (a : EnvelopingBimodule k (A k q) (twistedFiniteModule (sourceTwist q H)).carrier)
    (x : A.Simple q) :
    type_of% ((twistedEnvelopingEndpoint_tmul (sourceTwist q H) (A.Simple q) (A.Simple q)
      (Resolution.aInverseEndpoint q H).symm a x).trans (inverseEndpoint_inv_apply q H _)) :=
  (twistedEnvelopingEndpoint_tmul (sourceTwist q H) (A.Simple q) (A.Simple q)
      (Resolution.aInverseEndpoint q H).symm a x).trans (inverseEndpoint_inv_apply q H _)

omit [CharP k 2] [HasDerivedCategory (ModuleCat (T k q))] in
theorem evaluatedRestriction_eq :
    type_of% (twistedFiniteEndpoint_eq (sourceTwist q H) (A.simpleFiniteModule q)
      (evaluatedTwistEquiv q H) (Resolution.aInverseEndpoint q H)
      (fun a x => (inverseEndpoint_inv_apply q H _).trans (evaluatedTwistEquiv_tmul q H a x).symm)) :=
  twistedFiniteEndpoint_eq (sourceTwist q H) (A.simpleFiniteModule q)
    (evaluatedTwistEquiv q H) (Resolution.aInverseEndpoint q H)
    (fun a x => (inverseEndpoint_inv_apply q H _).trans (evaluatedTwistEquiv_tmul q H a x).symm)

omit [CharP k 2] [HasDerivedCategory (ModuleCat (T k q))] in
theorem evaluatedTwistEndpoint_eq :
    type_of% (twistedFiniteEndpoint_symm_eq (sourceTwist q H) (A.simpleFiniteModule q)
      (evaluatedTwistEquiv q H) (Resolution.aInverseEndpoint q H)
      (fun a x => (inverseEndpoint_inv_apply q H _).trans (evaluatedTwistEquiv_tmul q H a x).symm)) :=
  twistedFiniteEndpoint_symm_eq (sourceTwist q H) (A.simpleFiniteModule q)
    (evaluatedTwistEquiv q H) (Resolution.aInverseEndpoint q H)
    (fun a x => (inverseEndpoint_inv_apply q H _).trans (evaluatedTwistEquiv_tmul q H a x).symm)

theorem evaluatedTwistExt_scalar (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (hp : Resolution.NoPositivePowerOne q) (n : ℕ)
    (x : Resolution.ASelfExt q (3*n)) :
    selfExtIso (k := k) (evaluatedTwistIso q H) (3*n)
      (x.mapExactFunctor (evaluatedTwistFunctor q H)) = (((H⁻¹ : kˣ) : k)^n) • x := by
  have he := evaluatedTwistEndpoint_eq q H
  have hh := ResolutionProducts.exactFunctor_action_natIso (k := k)
    (evaluatedTwistFunctor q H) (Resolution.aInverseRestriction q H)
    (twistedEnvelopingRestrictionIso (sourceTwist q H))
    (ModuleBar.nativeResolution k (A k q) (A.Simple q))
    (Resolution.aInverseEndpoint q H) (3*n) x
  erw [← he] at hh
  exact hh.trans (Resolution.aInverseTwist_standard_scalar q H hq hq1 hp n x)

end ArExplicit.T

end

end OAI
