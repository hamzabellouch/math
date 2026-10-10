import OAI.Algebra.AuslanderReiten.Bar.ModuleBarNativeTransport
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorTransport
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorAugmentation
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorTwist

namespace OAI

noncomputable section
open CategoryTheory
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
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def nativeTensorEndpointIso : ExternalTensor.canonicalTensorObject k R S M N ≅
    (ExternalTensor.tensorRestriction k R S h j).obj
      (ExternalTensor.canonicalTensorObject k R S M N) := by
  let e₀ := nativeEndpointBase k R M h e he
  let f₀ := nativeEndpointBase k S N j f hf
  have he₀ := nativeEndpointBase_smul k R M h e he
  have hf₀ := nativeEndpointBase_smul k S N j f hf
  letI := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI := moduleCatBaseModule (k := k) (R := S) (ModuleCat.of S N)
  letI := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  letI := moduleCatBaseTower (k := k) (R := S) (ModuleCat.of S N)
  exact (ExternalTensor.tensorSemilinearEquiv k R S h j e₀ f₀ he₀ hf₀).toModuleIso

def nativeTensorTransport :
    ExternalTensor.complex k R S (nativeResolution k R M).complex (nativeResolution k S N).complex ⟶
    ((ExternalTensor.tensorRestriction k R S h j).mapHomologicalComplex (.down ℕ)).obj
      (ExternalTensor.complex k R S (nativeResolution k R M).complex (nativeResolution k S N).complex) :=
  ExternalTensor.transportComplex k R S h j
    (nativeResolution k R M).complex (nativeResolution k S N).complex
    (nativeTransportBase k R M h e he) (nativeTransportBase k S N j f hf)
    (nativeTransportBase_smul k R M h e he) (nativeTransportBase_smul k S N j f hf)
    (fun n x => (nativeTransportBase_d k R M h e he n x).symm)
    (fun n x => (nativeTransportBase_d k S N j f hf n x).symm)

omit [Module.Finite k R] [Module.Finite k S] [Module.Finite k M] [Module.Finite k N] in
theorem nativeTensorTransport_augmentation :
    (nativeTensorTransport k R S M N h j e f he hf).f 0 ≫
      (ExternalTensor.tensorRestriction k R S h j).map
        ((ExternalTensor.augmentation k R S (nativeResolution k R M) (nativeResolution k S N)).f 0) =
    (ExternalTensor.augmentation k R S (nativeResolution k R M) (nativeResolution k S N)).f 0 ≫
      (nativeTensorEndpointIso k R S M N h j e f he hf).hom := by
  apply ExternalTensor.hom_ext k R S (nativeResolution k R M).complex (nativeResolution k S N).complex
  intro a b hab
  have ha : a=0 := by omega
  have hb : b=0 := by omega
  subst a
  subst b
  change ExternalTensor.inclusion k R S _ _ 0 0 0 _ ≫
      (ExternalTensor.transportTerm k R S h j _ _
        (nativeTransportBase k R M h e he) (nativeTransportBase k S N j f hf)
        (nativeTransportBase_smul k R M h e he) (nativeTransportBase_smul k S N j f hf) 0 ≫ _) = _
  erw [← Category.assoc, ExternalTensor.inclusion_transportTerm, Category.assoc,
    ← Functor.map_comp, ExternalTensor.inclusion_augmentation,
    ← Category.assoc, ExternalTensor.inclusion_augmentation]
  let eP := nativeTransportBase k R M h e he 0
  let fP := nativeTransportBase k S N j f hf 0
  let e₀ := nativeEndpointBase k R M h e he
  let f₀ := nativeEndpointBase k S N j f hf
  have heP := nativeTransportBase_smul k R M h e he 0
  have hfP := nativeTransportBase_smul k S N j f hf 0
  have he₀ := nativeEndpointBase_smul k R M h e he
  have hf₀ := nativeEndpointBase_smul k S N j f hf
  let πM := (nativeResolution k R M).π.f 0
  let πN := (nativeResolution k S N).π.f 0
  have hπM := nativeTransportBase_π k R M h e he
  have hπN := nativeTransportBase_π k S N j f hf
  let := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  let := moduleCatBaseModule (k := k) (R := S) (ModuleCat.of S N)
  let := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  let := moduleCatBaseTower (k := k) (R := S) (ModuleCat.of S N)
  exact ExternalTensor.tensorSemilinear_natural k R S h j eP e₀.toLinearMap fP f₀.toLinearMap
    heP he₀ hfP hf₀ πM πN hπM hπN

end ArExplicit.ModuleBar

end

end OAI
