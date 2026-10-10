import OAI.Algebra.AuslanderReiten.Ext.ATwistExt
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorEndpointCoordinates
import OAI.Algebra.AuslanderReiten.Evaluation.TensorTwistEvaluation

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

abbrev aInverseRestriction := ExternalTensor.tensorRestriction k (ArExplicit.T k q) (ArExplicit.T k q)
  (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm

instance aInverseRestriction_isEquivalence : (aInverseRestriction q H).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (Algebra.TensorProduct.congr (TrivialExtension.twist H).symm
      (TrivialExtension.twist H).symm).toRingEquiv

def aInverseEndpoint : A.Simple q ≅ (aInverseRestriction q H).obj (A.Simple q) :=
  ModuleBar.tensorEndpointIso k (ArExplicit.T k q) (ArExplicit.T k q) (Simple q) (Simple q)
    (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H)

omit [CharP k 2] [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))] in
theorem aInverseEndpoint_apply (x : A.Simple q) : (aInverseEndpoint q H).hom.hom x = x := by
  exact (ModuleBar.tensorEndpointIso_apply k (ArExplicit.T k q) (ArExplicit.T k q)
    (Simple q) (Simple q) (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H) x).trans (by simp; rfl)

omit [CharP k 2] [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))] in
theorem aInverseRestriction_eq : aInverseRestriction q H =
    ModuleCat.restrictScalars (ArExplicit.T.sourceTwist q H).symm.toRingHom := rfl

omit [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))] in
theorem aInverseTwist_standard (n : ℕ) (x : ASelfExt q n) :
    type_of% (ModuleBar.tensorTwist_eq_exactFunctor k (ArExplicit.T k q) (ArExplicit.T k q)
    (Simple q) (Simple q) (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H) n x) :=
  ModuleBar.tensorTwist_eq_exactFunctor k (ArExplicit.T k q) (ArExplicit.T k q)
    (Simple q) (Simple q) (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H) n x

theorem aInverseTwist_standard_scalar (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (hp : NoPositivePowerOne q)
    (n : ℕ) (x : ASelfExt q (3*n)) :
    selfExtIso (k := k) (aInverseEndpoint q H).symm (3*n)
      (x.mapExactFunctor (aInverseRestriction q H)) = (((H⁻¹ : kˣ) : k)^n) • x := by
  rw [selfExtIso_apply]
  exact (aInverseTwist_standard q H (3*n) x).symm.trans
    (aInverseTwistExt_scalar q H hq hq1 hp n x)

end ArExplicit.Resolution

end

end OAI
