import OAI.Algebra.AuslanderReiten.Bar.NativeBarAugmentation
import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationAugmentation
import OAI.Algebra.AuslanderReiten.Bar.BarTensorRegularIsoCoordinates
import OAI.Algebra.AuslanderReiten.Ext.ExternalRegularMapPure
import OAI.Algebra.AuslanderReiten.Tensor.ExternalBalancedHomExt

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

@[simp] theorem nativeEndpointIso_tmul
    (m : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R 0)) (x : X) :
    (nativeEndpointIso k R X).hom (BalancedTensor.tmul m x) = (show R from m.value) • x := by
  change canonicalEquiv k R X 0 (BalancedTensor.tmul m x) = _
  rw [canonicalEquiv_tmul]
  rfl


private theorem regularMap_tmul_of_smul
    (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)) (f : M ⟶ AbsoluteBar.moduleObject k R 0)
    (m : EnvelopingBimodule k R M) (x y : X)
    (h : (show R from f m.value) • x = y) :
    regularMap k R X M f (BalancedTensor.tmul m x) = y :=
  (regularMap_tmul k R X M f m x).trans h

private theorem namedRegularMap_tmul_of_smul
    (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)) (f : M ⟶ AbsoluteBar.moduleObject k R 0)
    (g : (EnvelopingBimodule.evaluationFunctor k R X).obj M ⟶ X)
    (hg : g = regularMap k R X M f)
    (m : EnvelopingBimodule k R M) (x y : X)
    (h : (show R from f m.value) • x = y) :
    g (BalancedTensor.tmul m x) = y :=
  (congrArg (fun q : (EnvelopingBimodule.evaluationFunctor k R X).obj M ⟶ X =>
    q (BalancedTensor.tmul m x)) hg).trans
      (regularMap_tmul_of_smul k R X M f m x y h)

end ArExplicit.BarBalanced

namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
local notation "UA" => AbsoluteBar.moduleObject k A 0
local notation "UB" => AbsoluteBar.moduleObject k B 0
local notation "XY" => ExternalTensor.moduleObject k A B X Y
local notation "E" => EnvelopingBimodule.evaluationFunctor k (A ⊗[k] B) XY

-- Keep the scalar-ring and evaluation-object presentations used by the endpoint
-- maps. This avoids expanding their tensor-module structures when specializing
-- extensionality to the degree-zero bar objects.
private theorem exterior_raw_hom_ext
    (M : ModuleCat.{u} (AbsoluteBar.Enveloping k A)) (N : ModuleCat.{u} (AbsoluteBar.Enveloping k B))
    (Z : ModuleCat.{u} (A ⊗[k] B))
    (f : (productEvaluation k A B X Y).obj
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) M N) ⟶ Z)
    (g : (E).obj (ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) M N)) ⟶ Z)
    (h : ∀ (a : EnvelopingBimodule k A M) (b : EnvelopingBimodule k B N) (x : X) (y : Y),
      f (BalancedTensor.tmul ((bimoduleCoordinates k A B M N).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      g (BalancedTensor.tmul ((bimoduleCoordinates k A B M N).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y)))) : f = g :=
  exterior_hom_ext k A B M N X Y Z f g h

def factorRegularEndpoint :
    (productEvaluation k A B X Y).obj
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) UA UB) ⟶ XY :=
  totalEndpointMap k A B X Y (BarBalanced.nativeEndpointIso k A X).hom
    (BarBalanced.nativeEndpointIso k B Y).hom

def productRegularEndpoint :
    (productEvaluation k A B X Y).obj
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) UA UB) ⟶ XY :=
  BarBalanced.regularMap k (A ⊗[k] B) XY
    (ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) UA UB))
    (barTensorZeroEquiv k A B).toModuleIso.hom

theorem factorRegularEndpoint_pure (a : EnvelopingBimodule k A UA)
    (b : EnvelopingBimodule k B UB) (x : X) (y : Y) :
    factorRegularEndpoint k A B X Y (BalancedTensor.tmul
      ((bimoduleCoordinates k A B UA UB).symm (a ⊗ₜ[k] b))
      ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      ((show A from a.value) • x) ⊗ₜ[k] ((show B from b.value) • y) := by
  change ExternalTensor.map k A B (BarBalanced.nativeEndpointIso k A X).hom.hom
    (BarBalanced.nativeEndpointIso k B Y).hom.hom
    (shuffle k A B UA UB X Y (BalancedTensor.tmul
      ((bimoduleCoordinates k A B UA UB).symm (a ⊗ₜ[k] b))
      ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y)))) = _
  erw [shuffle_pure, ExternalTensor.map_tmul]
  erw [BarBalanced.nativeEndpointIso_tmul k A X a x, BarBalanced.nativeEndpointIso_tmul k B Y b y]

private theorem productRegularEndpoint_eq_map :
    productRegularEndpoint k A B X Y =
      BarBalanced.regularMap k (A ⊗[k] B) XY
        (ExternalTensor.envelopingObject k A B
          (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) UA UB))
        (barTensorZeroEquiv k A B).toModuleIso.hom := rfl

private theorem productRegularEndpoint_scalar_pure
    (left : EnvelopingBimodule k A UA) (right : EnvelopingBimodule k B UB) :
    (show A ⊗[k] B from (barTensorZeroEquiv k A B).toModuleIso.hom
      ((bimoduleCoordinates k A B UA UB).symm (left ⊗ₜ[k] right)).value) =
      (show A from left.value) ⊗ₜ[k] (show B from right.value) := by
  rw [bimoduleCoordinates_symm_tmul]
  exact barTensorZeroIso_tmul k A B left.value right.value

private theorem productRegularEndpoint_scalar_action (a : EnvelopingBimodule k A UA)
    (b : EnvelopingBimodule k B UB) (x : X) (y : Y) :
    type_of% ((congrArg (fun scalar : A ⊗[k] B => scalar •
      (ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))
      (productRegularEndpoint_scalar_pure k A B a b)).trans
        (ExternalTensor.smul_tmul k A B X Y a.value b.value x y)) :=
  (congrArg (fun scalar : A ⊗[k] B => scalar •
    (ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))
    (productRegularEndpoint_scalar_pure k A B a b)).trans
      (ExternalTensor.smul_tmul k A B X Y a.value b.value x y)

private abbrev productRegularEndpointPureProof (a : EnvelopingBimodule k A UA)
    (b : EnvelopingBimodule k B UB) (x : X) (y : Y) :=
  BarBalanced.namedRegularMap_tmul_of_smul k (A ⊗[k] B) XY
    (ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) UA UB))
    (barTensorZeroEquiv k A B).toModuleIso.hom
    (productRegularEndpoint k A B X Y) (productRegularEndpoint_eq_map k A B X Y)
    ((bimoduleCoordinates k A B UA UB).symm (a ⊗ₜ[k] b))
    ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))
    (((show A from a.value) • x) ⊗ₜ[k] ((show B from b.value) • y))
    (productRegularEndpoint_scalar_action k A B X Y a b x y)

theorem productRegularEndpoint_pure (a : EnvelopingBimodule k A UA)
    (b : EnvelopingBimodule k B UB) (x : X) (y : Y) :
    type_of% (productRegularEndpointPureProof k A B X Y a b x y) :=
  productRegularEndpointPureProof k A B X Y a b x y


private theorem regularEndpoint_pure_eq
    (left : EnvelopingBimodule k A UA) (right : EnvelopingBimodule k B UB)
    (first : X) (second : Y) :
    type_of% ((factorRegularEndpoint_pure k A B X Y left right first second).trans
      (productRegularEndpoint_pure k A B X Y left right first second).symm) :=
  (factorRegularEndpoint_pure k A B X Y left right first second).trans
    (productRegularEndpoint_pure k A B X Y left right first second).symm

private theorem regularEndpoint_ext :
    type_of% (exterior_raw_hom_ext k A B X Y UA UB XY) :=
  exterior_raw_hom_ext k A B X Y UA UB XY

private theorem regularEndpoint_eq_aux :
    type_of% (regularEndpoint_ext k A B X Y
      (factorRegularEndpoint k A B X Y) (productRegularEndpoint k A B X Y)
      (regularEndpoint_pure_eq k A B X Y)) :=
  regularEndpoint_ext k A B X Y
    (factorRegularEndpoint k A B X Y) (productRegularEndpoint k A B X Y)
    (regularEndpoint_pure_eq k A B X Y)

theorem regularEndpoint_eq :
    totalEndpointMap k A B X Y (BarBalanced.nativeEndpointIso k A X).hom
      (BarBalanced.nativeEndpointIso k B Y).hom =
    (E).map (barTensorZeroEquiv k A B).toModuleIso.hom ≫
      (BarBalanced.nativeEndpointIso k (A ⊗[k] B) XY).hom :=
  regularEndpoint_eq_aux k A B X Y

end ArExplicit.ExternalBalanced

end

end OAI
