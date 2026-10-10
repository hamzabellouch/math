import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionCubicConjugate
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorExt

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
variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]
variable {B X : ModuleCat.{u} (R ⊗[k] S)}

omit [HasDerivedCategory (ModuleCat R)] [HasDerivedCategory (ModuleCat S)] in
theorem resolutionExt_nativeFirst
    (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
    (P : ProjectiveResolution B) (e : B ≅ X)
    (j : X ≅ ExternalTensor.canonicalTensorObject k R S M N)
    (φ : ProjectiveResolution.Hom P
      (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N))
      (e.hom ≫ j.hom))
    (p₀ : P.complex.X 3 ⟶ P.complex.X 0)
    (f : P.complex.X 3 ⟶ X) (hf : P.complex.d 4 3 ≫ f = 0)
    (hfc : f = p₀ ≫ P.π.f 0 ≫ e.hom)
    (hc : p₀ ≫ φ.hom.f 0 = φ.hom.f 3 ≫
      ModuleCat.ofHom (ExternalTensor.firstCubic k R S (complex k R M) (complex k S N)
        (cubicMap k R M p) 0)) :
    selfExtIso (k := k) j 3 ((Ext.mk₀ e.inv).comp (P.extMk f 4 rfl hf) (zero_add _)) =
      nativeTensorFirst k R S M N p hp :=
  resolutionExt_cubic_conjugate (k := k) P
    (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N))
    e j φ p₀
    (ExternalTensor.firstComparison k R S (nativeResolution k R M) (nativeResolution k S N)
      (nativeCubicMap k R M p))
    (ExternalTensor.firstComparison_comm k R S (nativeResolution k R M) (nativeResolution k S N)
      (nativeCubicMap k R M p) (nativeCubicMap_comm k R M p hp))
    f hf hfc hc

omit [HasDerivedCategory (ModuleCat R)] [HasDerivedCategory (ModuleCat S)] in
theorem resolutionExt_nativeSecond
    (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)
    (P : ProjectiveResolution B) (e : B ≅ X)
    (j : X ≅ ExternalTensor.canonicalTensorObject k R S M N)
    (φ : ProjectiveResolution.Hom P
      (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N))
      (e.hom ≫ j.hom))
    (p₀ : P.complex.X 3 ⟶ P.complex.X 0)
    (f : P.complex.X 3 ⟶ X) (hf : P.complex.d 4 3 ≫ f = 0)
    (hfc : f = p₀ ≫ P.π.f 0 ≫ e.hom)
    (hc : p₀ ≫ φ.hom.f 0 = φ.hom.f 3 ≫
      ModuleCat.ofHom (ExternalTensor.secondCubic k R S (complex k R M) (complex k S N)
        (cubicMap k S N r) 0)) :
    selfExtIso (k := k) j 3 ((Ext.mk₀ e.inv).comp (P.extMk f 4 rfl hf) (zero_add _)) =
      nativeTensorSecond k R S M N r hr :=
  resolutionExt_cubic_conjugate (k := k) P
    (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N))
    e j φ p₀
    (ExternalTensor.secondComparison k R S (nativeResolution k R M) (nativeResolution k S N)
      (nativeCubicMap k S N r))
    (ExternalTensor.secondComparison_comm k R S (nativeResolution k R M) (nativeResolution k S N)
      (nativeCubicMap k S N r) (nativeCubicMap_comm k S N r hr))
    f hf hfc hc

end ArExplicit.ModuleBar

end

end OAI
