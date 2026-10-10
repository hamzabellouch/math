import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorTransport
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorHomTransport
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorHomPairTransport

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
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

abbrev nativeTensorHomTransport :=
  ExternalTensor.homTensorMap k R S (nativeResolution k R M) (nativeResolution k S N)
    (ModuleCat.of R M) (ModuleCat.of S N)
    (nativeHomTransport k R M h e he) (nativeHomTransport k S N j f hf)

omit [Module.Finite k R] [Module.Finite k S] [Module.Finite k M] [Module.Finite k N] in
@[reassoc] theorem nativeTensorTransport_inclusion (a b n : ℕ) (hab : a+b=n) :
    ExternalTensor.inclusion k R S (nativeResolution k R M).complex (nativeResolution k S N).complex
        a b n hab ≫ (nativeTensorTransport k R S M N h j e f he hf).f n =
    ExternalTensor.transportSummand k R S h j
      (nativeResolution k R M).complex (nativeResolution k S N).complex
      (nativeTransportBase k R M h e he) (nativeTransportBase k S N j f hf)
      (nativeTransportBase_smul k R M h e he) (nativeTransportBase_smul k S N j f hf) a b ≫
        (ExternalTensor.tensorRestriction k R S h j).map
          (ExternalTensor.inclusion k R S (nativeResolution k R M).complex
            (nativeResolution k S N).complex a b n hab) :=
  ExternalTensor.inclusion_transportTerm k R S h j _ _ _ _ _ _ a b n hab

theorem nativeTensorHomTransport_forward (n : ℕ)
    (x : (ExternalTensor.complex k R S (nativeResolution k R M).complex
      (nativeResolution k S N).complex).X n ⟶ ExternalTensor.canonicalTensorObject k R S M N) :
    ModuleCat.ofHom
      (X := (ExternalTensor.complex k R S (nativeResolution k R M).complex
        (nativeResolution k S N).complex).X n)
      (Y := ExternalTensor.canonicalTensorObject k R S M N)
      (((nativeTensorHomTransport k R S M N h j e f he hf).f n).hom x.hom) ≫
        (nativeTensorEndpointIso k R S M N h j e f he hf).hom =
    (nativeTensorTransport k R S M N h j e f he hf).f n ≫
      (ExternalTensor.tensorRestriction k R S h j).map x := by
  apply ExternalTensor.hom_ext k R S (nativeResolution k R M).complex (nativeResolution k S N).complex
  intro a b hab
  erw [nativeTensorTransport_inclusion_assoc, ← Functor.map_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let y := (ExternalTensor.homCochainTermEquiv k R S
    (nativeResolution k R M).complex (nativeResolution k S N).complex
    (ModuleCat.of R M) (ModuleCat.of S N) n).symm x.hom
  let c := ExternalTensor.homCochainTermCoordinates k R S
    (nativeResolution k R M).complex (nativeResolution k S N).complex
    (ModuleCat.of R M) (ModuleCat.of S N) n y ⟨(a,b),hab⟩
  have hout := ExternalTensor.homCochainTermEquiv_restrict k R S
    (nativeResolution k R M).complex (nativeResolution k S N).complex
    (ModuleCat.of R M) (ModuleCat.of S N) n y ⟨(a,b),hab⟩
  dsimp only [y] at hout
  erw [LinearEquiv.apply_symm_apply] at hout
  have htrans := ExternalTensor.homTensorMap_restrict k R S
    (nativeResolution k R M) (nativeResolution k S N) (ModuleCat.of R M) (ModuleCat.of S N)
    (nativeHomTransport k R M h e he) (nativeHomTransport k S N j f hf) n x.hom ⟨(a,b),hab⟩
  let e₀ := nativeEndpointBase k R M h e he
  let f₀ := nativeEndpointBase k S N j f hf
  let a₀ := nativeTransportBase k R M h e he a
  let b₀ := nativeTransportBase k S N j f hf b
  let α := ((nativeHomTransport k R M h e he).f a).hom
  let β := ((nativeHomTransport k S N j f hf).f b).hom
  have hα := nativeHomTransport_apply k R M h e he a
  have hβ := nativeHomTransport_apply k S N j f hf b
  let mapped : (ExternalTensor.complex k R S (nativeResolution k R M).complex
      (nativeResolution k S N).complex).X n →ₗ[R ⊗[k] S]
      ExternalTensor.canonicalTensorObject k R S M N :=
    ((nativeTensorHomTransport k R S M N h j e f he hf).f n).hom x.hom
  let inc := ExternalTensor.inclusion k R S (nativeResolution k R M).complex
    (nativeResolution k S N).complex a b n hab
  let := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  let := moduleCatBaseModule (k := k) (R := S) (ModuleCat.of S N)
  let := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  let := moduleCatBaseTower (k := k) (R := S) (ModuleCat.of S N)
  have hp := ExternalTensor.homMap_transport k R S a₀ b₀ e₀ f₀ α β hα hβ c z
  have hpf := congrArg (TensorProduct.congr e₀ f₀) hp
  erw [LinearEquiv.apply_symm_apply] at hpf
  change (TensorProduct.congr e₀ f₀) (mapped (inc.hom z)) = _
  erw [show mapped (inc.hom z) =
      ExternalTensor.homMap k R S (TensorProduct.map α β c) z from
        LinearMap.congr_fun htrans z]
  erw [hpf]
  exact (LinearMap.congr_fun hout (TensorProduct.map a₀ b₀ z)).symm

theorem nativeTensorHomTransport_apply (n : ℕ)
    (x : (ExternalTensor.complex k R S (nativeResolution k R M).complex
      (nativeResolution k S N).complex).X n ⟶ ExternalTensor.canonicalTensorObject k R S M N) :
    ModuleCat.ofHom
      (X := (ExternalTensor.complex k R S (nativeResolution k R M).complex
        (nativeResolution k S N).complex).X n)
      (Y := ExternalTensor.canonicalTensorObject k R S M N)
      (((nativeTensorHomTransport k R S M N h j e f he hf).f n).hom x.hom) =
    ((nativeTensorTransport k R S M N h j e f he hf).f n ≫
      (ExternalTensor.tensorRestriction k R S h j).map x) ≫
        (nativeTensorEndpointIso k R S M N h j e f he hf).inv := by
  apply (cancel_mono (nativeTensorEndpointIso k R S M N h j e f he hf).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact nativeTensorHomTransport_forward k R S M N h j e f he hf n x

end ArExplicit.ModuleBar

end

end OAI
