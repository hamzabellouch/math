import OAI.Algebra.AuslanderReiten.Ext.ExtKunnethMap
import OAI.Algebra.AuslanderReiten.Ext.TTensorTwist
import OAI.Algebra.AuslanderReiten.Ext.AExtPolynomial
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarNativeTwist
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorTwist
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorAction

import OAI.Algebra.AuslanderReiten.Homology.TTwistFactor
import OAI.Algebra.AuslanderReiten.Homology.LinearEquivActionTransfer

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable (h : R ≃ₐ[k] R) (j : S ≃ₐ[k] S) (e : M ≃ₗ[k] M) (f : N ≃ₗ[k] N)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (hf : ∀ a n, f (a • n) = j a • f n)
variable (α : ∀ n, Ext (ModuleCat.of R M) (ModuleCat.of R M) n →ₗ[k]
  Ext (ModuleCat.of R M) (ModuleCat.of R M) n)
variable (β : ∀ n, Ext (ModuleCat.of S N) (ModuleCat.of S N) n →ₗ[k]
  Ext (ModuleCat.of S N) (ModuleCat.of S N) n)
variable (hα : ∀ n, twistExtAction k R M h e he n = α n)
variable (hβ : ∀ n, twistExtAction k S N j f hf n = β n)
variable (Φ : ∀ n, (ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n) →ₗ[k] (ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n))
variable (hΦ : ∀ n (x : (ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n)) (p : ExternalTensor.Diagonal n), Φ n x p = TensorProduct.map (α p.val.1) (β p.val.2) (x p))
include hα hβ hΦ

private theorem tensorTwist_image_scalar (n : ℕ) (c : k)
    (hscalar : ∀ z, Φ n z = c • z)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorKunneth k R S M N n (tensorTwist k R S M N h j e f he hf n x) =
      c • tensorKunneth k R S M N n x :=
  (tensorTwist_kunneth_action k R S M N h j e f he hf α β hα hβ Φ hΦ n x).trans
    (hscalar _)

private theorem tensorTwist_scalar (n : ℕ) (c : k)
    (hscalar : ∀ z, Φ n z = c • z)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorTwist k R S M N h j e f he hf n x = c • x :=
  (tensorKunneth k R S M N n).injective
    ((tensorTwist_image_scalar k R S M N h j e f he hf α β hα hβ Φ hΦ n c hscalar x).trans
      ((tensorKunneth k R S M N n).map_smul c x).symm)

end ArExplicit.ModuleBar

namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
local notation "T" => ArExplicit.T k q
local notation "S" => ModuleCat.of T (Simple q)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

abbrev aCanonicalInverseTwistExt (n : ℕ) :=
  ModuleBar.nativeTensorTwist k T T (Simple q) (Simple q)
    (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H) n

omit [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))] in
theorem aCanonicalInverseTwistExt_kunneth (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k T T (Simple q) (Simple q))
      (ExternalTensor.canonicalTensorObject k T T (Simple q) (Simple q)) n) :
    type_of% (ModuleBar.nativeTensorTwist_kunneth_action k T T (Simple q) (Simple q)
    (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (tInverseTwistExt q H) (tInverseTwistExt q H)
    (tInverseTwistExt_factor q H) (tInverseTwistExt_factor q H)
    (tTensorInverseTwist q H) (tTensorInverseTwist_apply q H) n x) :=
  ModuleBar.nativeTensorTwist_kunneth_action k T T (Simple q) (Simple q)
    (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (tInverseTwistExt q H) (tInverseTwistExt q H)
    (tInverseTwistExt_factor q H) (tInverseTwistExt_factor q H)
    (tTensorInverseTwist q H) (tTensorInverseTwist_apply q H) n x

abbrev aInverseTwistExt (n : ℕ) :=
  ModuleBar.tensorTwist k T T (Simple q) (Simple q)
    (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H) n

omit [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))] in
theorem aInverseTwistExt_kunneth (n : ℕ) (x : ASelfExt q n) :
    type_of% (ModuleBar.tensorTwist_kunneth_action k T T (Simple q) (Simple q)
    (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (tInverseTwistExt q H) (tInverseTwistExt q H)
    (tInverseTwistExt_factor q H) (tInverseTwistExt_factor q H)
    (tTensorInverseTwist q H) (tTensorInverseTwist_apply q H) n x) :=
  ModuleBar.tensorTwist_kunneth_action k T T (Simple q) (Simple q)
    (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (tInverseTwistExt q H) (tInverseTwistExt q H)
    (tInverseTwistExt_factor q H) (tInverseTwistExt_factor q H)
    (tTensorInverseTwist q H) (tTensorInverseTwist_apply q H) n x

variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (hp : NoPositivePowerOne q)
include hq hq1 hp

private abbrev inverseTwistImageScalarProof (n : ℕ) (x : ASelfExt q (3*n)) :=
  ModuleBar.tensorTwist_image_scalar k T T (Simple q) (Simple q)
    (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (tInverseTwistExt q H) (tInverseTwistExt q H)
    (tInverseTwistExt_factor q H) (tInverseTwistExt_factor q H)
    (tTensorInverseTwist q H) (tTensorInverseTwist_apply q H)
    (3*n) (((H⁻¹ : kˣ) : k)^n) (tTensorInverseTwist_scalar q H hq hq1 hp n) x

theorem aInverseTwistExt_image_scalar (n : ℕ) (x : ASelfExt q (3*n)) :
    type_of% (inverseTwistImageScalarProof q H hq hq1 hp n x) :=
  inverseTwistImageScalarProof q H hq hq1 hp n x

private abbrev inverseTwistScalarProof (n : ℕ) (x : ASelfExt q (3*n)) :=
  ModuleBar.tensorTwist_scalar k T T (Simple q) (Simple q)
    (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (tInverseTwistExt q H) (tInverseTwistExt q H)
    (tInverseTwistExt_factor q H) (tInverseTwistExt_factor q H)
    (tTensorInverseTwist q H) (tTensorInverseTwist_apply q H)
    (3*n) (((H⁻¹ : kˣ) : k)^n) (tTensorInverseTwist_scalar q H hq hq1 hp n) x

theorem aInverseTwistExt_scalar (n : ℕ) (x : ASelfExt q (3*n)) :
    type_of% (inverseTwistScalarProof q H hq hq1 hp n x) :=
  inverseTwistScalarProof q H hq hq1 hp n x

end ArExplicit.Resolution

end

end OAI
