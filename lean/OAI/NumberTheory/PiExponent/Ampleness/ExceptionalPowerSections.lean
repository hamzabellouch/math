import OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional
import OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry
namespace PiExponentSeshadri.Geometry
variable {X Y : Scheme}

lemma InvertibleLocal.pullback_frame_equation {I : X.IdealSheafData} {f : Y ⟶ X}
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (U : Y.affineOpens) (V : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    (I.ideal V).map (f.appLE V.1 U.1 hUV).hom =
      Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι} := by
  let g : O U.1.toScheme ⟶ O U.1.toScheme :=
    e.inv ≫ PiExponentSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι
  have H : ((I.comap f).comap U.1.ι).ideal ⟨⊤,isAffineOpen_top _⟩ =
      Ideal.span {endValue g} := by
    change _ = Ideal.span {UnitEndomorphism.equation g ⊤}
    rw [← UnitEndomorphism.image_principal g ⊤,
      ← PiExponentSeshadri.InvertibleLocal.restricted_image_on_chart J ι hJ U.1.ι
        ⟨⊤,isAffineOpen_top _⟩ V (by simpa only [Scheme.Opens.ι_image_top] using hUV)]
    ext r
    change (∃ s, (PiExponentSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι).val.app (.op ⊤) s = r) ↔
      ∃ s, (PiExponentSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι).val.app (.op ⊤)
        (e.inv.val.app (.op ⊤) s) = r
    constructor
    · rintro ⟨s,hs⟩
      refine ⟨e.hom.val.app (.op ⊤) s,?_⟩
      have ht : e.inv.val.app (.op ⊤) (e.hom.val.app (.op ⊤) s) = s :=
        congrArg (fun k : J.sheaf.restrict U.1.ι ⟶ J.sheaf.restrict U.1.ι =>
          k.val.app (.op ⊤) s) e.hom_inv_id
      rw [ht]; exact hs
    · rintro ⟨s,hs⟩; exact ⟨e.inv.val.app (.op ⊤) s,hs⟩
  rw [IdealPullback.comap_ι_top,IdealPullback.comap_ideal I f U V hUV] at H
  have H' := congrArg (Ideal.map U.1.topIso.hom.hom) H
  rw [Ideal.map_map,Ideal.map_span,Set.image_singleton] at H'
  have hi : U.1.topIso.hom.hom.comp U.1.topIso.inv.hom = RingHom.id _ := by
    ext x; exact U.1.topIso.inv_hom_id_apply x
  rw [hi,Ideal.map_id] at H'
  exact H'

theorem framed_section_range {Z : Scheme} {M : Z.Modules}
    (e : M ≅ O Z) (a : M ⟶ O Z) :
    (a.val.app (.op ⊤)).hom.range =
      Ideal.span {endValue (e.inv ≫ a)} := by
  rw [show endValue (e.inv ≫ a) =
    UnitEndomorphism.equation (e.inv ≫ a) ⊤ from rfl,
    ← UnitEndomorphism.image_principal]
  ext r
  change (∃ s, a.val.app (.op ⊤) s = r) ↔
    ∃ s, a.val.app (.op ⊤) (e.inv.val.app (.op ⊤) s) = r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.hom.val.app (.op ⊤) s, ?_⟩
    have h : e.inv.val.app (.op ⊤) (e.hom.val.app (.op ⊤) s) = s := by
      exact congrArg (fun k : M ⟶ M => k.val.app (.op ⊤) s) e.hom_inv_id
    rw [h]
    exact hs
  · rintro ⟨s, hs⟩
    exact ⟨e.inv.val.app (.op ⊤) s, hs⟩

theorem idealPower_restricted_range (f : Y ⟶ X) (I : X.IdealSheafData)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (n : ℕ) (U : Y.affineOpens) (V : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    ((PiExponentSeshadri.InvertibleLocal.restrictedInclusion (J.pow n)
      (idealPowerInclusion J ι n) U.1.ι).val.app (.op ⊤)).hom.range =
      (((I.ideal V)^n).map (f.appLE V.1 U.1 hUV).hom).map U.1.topIso.inv.hom := by
  erw [framed_section_range (idealPowerFrame J U.1 e n)]
  have h := idealPowerInclusion_ideal J ι U e n
  rw [← InvertibleLocal.pullback_frame_equation J ι hJ U V hUV, ← Ideal.map_pow] at h
  have h' := congrArg (Ideal.map U.1.topIso.inv.hom) h
  rw [Ideal.map_span, Set.image_singleton] at h'
  simpa only [affineMapCoefficient, U.1.topIso.hom_inv_id_apply,
    PiExponentSeshadri.InvertibleLocal.restrictedInclusion, Category.assoc] using! h'

def powerChartIdeal (f : Y ⟶ X) (I : X.IdealSheafData) (n : ℕ)
    (U : Y.affineOpens) (V : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    Ideal Γ(U.1.toScheme, ⊤) :=
  (((I.ideal V)^n).map (f.appLE V.1 U.1 hUV).hom).map U.1.topIso.inv.hom

private abbrev powerSections (J : LineBundle Y) (n : ℕ) (U : Y.Opens) :
    ModuleCat Γ(U.toScheme, ⊤) := ((J.pow n).sheaf.restrict U.ι).val.obj (.op ⊤)

def idealPowerSectionsEquiv (f : Y ⟶ X) (I : X.IdealSheafData)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (n : ℕ) (U : Y.affineOpens) (V : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    powerSections J n U.1 ≃ₗ[Γ(U.1.toScheme, ⊤)]
      ↥(powerChartIdeal f I n U V hUV) := by
  letI : Mono ι := hJ.1
  letI := idealPowerInclusion_mono J ι n
  let a := PiExponentSeshadri.InvertibleLocal.restrictedInclusion (J.pow n)
    (idealPowerInclusion J ι n) U.1.ι
  have ha : Mono (C := U.1.toScheme.Modules) a :=
    @PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono Y U.1.toScheme
      (J.pow n) (idealPowerInclusion J ι n) U.1.ι inferInstance
      (@idealPowerInclusion_mono Y J ι hJ.1 n)
  have hinj : Function.Injective (a.val.app (.op ⊤)) := by
    let : Mono a.val :=
      @Functor.map_mono _ _ _ _ (Scheme.Modules.toPresheafOfModules U.1.toScheme)
        inferInstance _ _ a ha
    exact PresheafOfModules.injective_of_mono a.val (.op ⊤)
  let φ : powerSections J n U.1 →ₗ[Γ(U.1.toScheme, ⊤)]
      Γ(U.1.toScheme, ⊤) := (a.val.app (.op ⊤)).hom
  have hr : φ.range = (powerChartIdeal f I n U V hUV : Submodule Γ(U.1.toScheme, ⊤) _) :=
    idealPower_restricted_range f I J ι hJ n U V hUV e
  exact (LinearEquiv.ofInjective φ hinj).trans (LinearEquiv.ofEq _ _ hr)

theorem idealPowerSectionsEquiv_apply (f : Y ⟶ X) (I : X.IdealSheafData)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (n : ℕ) (U : Y.affineOpens) (V : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (s : powerSections J n U.1) :
    (idealPowerSectionsEquiv f I J ι hJ n U V hUV e s).val =
      (PiExponentSeshadri.InvertibleLocal.restrictedInclusion (J.pow n)
        (idealPowerInclusion J ι n) U.1.ι).val.app (.op ⊤) s := rfl

end PiExponentSeshadri.Geometry
end

end OAI
