import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections
import OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
namespace PiExponent.ExceptionalAffineChart
open PiExponentSeshadri.IdealPullback
variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}
variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))

def chartOpen : Y.affineOpens :=
  ⟨j.opensRange, isAffineOpen_opensRange _⟩

def affineGammaEquiv {Y : Scheme} {A : CommRingCat} (g : Y ≅ Spec A) :
    Γ(Y,⊤) ≃+* A :=
  (Scheme.Γ.mapIso g.symm.op ≪≫ Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv

def chartFunctionsEquiv : Γ((chartOpen j).1.toScheme, ⊤) ≃+* A :=
  affineGammaEquiv (j.isoOpensRange.symm)

def chartPowerIdeal (n : ℕ) : Ideal Γ((chartOpen j).1.toScheme, ⊤) :=
  powerChartIdeal (f) (specIdeal I) n (chartOpen j)
    ⟨⊤, isAffineOpen_top _⟩ (by simp)

theorem chartPowerIdeal_eq (n : ℕ) :
    chartPowerIdeal I f j n =
      ((((specIdeal I).comap f)^n).comap (chartOpen j).1.ι).ideal
        ⟨⊤, isAffineOpen_top _⟩ := by
  change powerChartIdeal f (specIdeal I) n (chartOpen j)
    ⟨⊤, isAffineOpen_top _⟩ _ = _
  simp only [powerChartIdeal]
  have hlocal := PiExponentSeshadri.IdealPullback.comap_ideal ((specIdeal I)^n)
    f (chartOpen j) ⟨⊤, isAffineOpen_top _⟩ (by simp)
  have hpow := congrArg (fun K : Y.IdealSheafData => K.ideal (chartOpen j))
    (PiExponentSeshadri.IdealPullback.comap_pow (specIdeal I) f n)
  exact (congrArg (Ideal.map (chartOpen j).1.topIso.inv.hom)
    (hlocal.symm.trans hpow)).trans
      (PiExponentSeshadri.IdealPullback.comap_ι_top
        (((specIdeal I).comap f)^n) (chartOpen j)).symm

include hf in

theorem map_chartPowerIdeal (n : ℕ) :
    (chartPowerIdeal I f j n).map (chartFunctionsEquiv j).toRingHom =
      (I^n).map (φ) := by
  let : IsAffine j.opensRange.toScheme := isAffineOpen_opensRange j
  have hlocal : ((((specIdeal I).comap f)^n).comap j).ideal
      ⟨⊤, isAffineOpen_top _⟩ =
      ((I^n).map (φ)).map
        (Scheme.ΓSpecIso (CommRingCat.of (A))).inv.hom := by
    rw [← PiExponentSeshadri.IdealPullback.comap_pow,
      ← PiExponentSeshadri.IdealPullback.specIdeal_pow,
      ← Scheme.IdealSheafData.comap_comp, hf,
      specIdeal_comap, specIdeal_top]
  have hmap : (chartPowerIdeal I f j n).map
      (j.isoOpensRange.hom.appTop.hom) =
      ((((specIdeal I).comap f)^n).comap j).ideal
        ⟨⊤, isAffineOpen_top _⟩ := by
    erw [chartPowerIdeal_eq, ← PiExponentSeshadri.IdealPullback.comap_top,
      ← Scheme.IdealSheafData.comap_comp]
    change (((specIdeal I).comap f ^ n).comap (j.isoOpensRange.hom ≫ j.opensRange.ι)).ideal _ = _
    rw [j.isoOpensRange_hom_ι]
  change (chartPowerIdeal I f j n).map
    ((Scheme.ΓSpecIso (CommRingCat.of (A))).hom.hom.comp
      (j.isoOpensRange.hom.appTop.hom)) = _
  erw [← Ideal.map_map, hmap, hlocal, Ideal.map_map]
  have hi : (Scheme.ΓSpecIso (CommRingCat.of (A))).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (A))).inv.hom = RingHom.id _ := by
    apply RingHom.ext
    intro r
    exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply r
  rw [hi, Ideal.map_id]

def idealMapAddEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (J : Ideal A) : J ≃+ J.map e.toRingHom :=
  AddEquiv.ofBijective
    (show J →+ J.map e.toRingHom from
      { toFun := fun x => ⟨e x, Ideal.mem_map_of_mem _ x.property⟩
        map_zero' := by ext; exact e.map_zero
        map_add' := by intro x y; ext; exact e.map_add x y })
    ⟨by intro x y h; exact Subtype.ext (e.injective (congrArg Subtype.val h)), by
      intro y
      obtain ⟨x, hx, he⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp y.property
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩⟩

def sectionsEquiv (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
    (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
    (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme) (n : ℕ) :
    ((L.pow n).sheaf.restrict (chartOpen j).1.ι).val.obj (.op ⊤) ≃+ ↥((I^n).map φ) :=
  (idealPowerSectionsEquiv f (specIdeal I) L ι hL n (chartOpen j)
    ⟨⊤, isAffineOpen_top _⟩ (by simp) e).toAddEquiv |>.trans
      ((idealMapAddEquiv (chartFunctionsEquiv j) (chartPowerIdeal I f j n)).trans
        ((LinearEquiv.ofEq _ _ (map_chartPowerIdeal I f j φ hf n)).toAddEquiv))

theorem sectionsEquiv_apply (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
    (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
    (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme) (n : ℕ)
    (s : ((L.pow n).sheaf.restrict (chartOpen j).1.ι).val.obj (.op ⊤)) :
    (sectionsEquiv I f j φ hf L ι hL e n s).val =
      chartFunctionsEquiv j
        ((PiExponentSeshadri.InvertibleLocal.restrictedInclusion (L.pow n)
          (idealPowerInclusion L ι n) (chartOpen j).1.ι).val.app (.op ⊤) s) := rfl

def idealChartFrame (L : Y.IdealSheafData)
    (r : Γ(Spec (CommRingCat.of A), ⊤))
    (hprincipal : (L.comap j).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r})
    (hregular : IsLeftRegular r) :
    (PiExponentSeshadri.IdealModule.closedModule L).restrict (chartOpen j).1.ι ≅
      O (chartOpen j).1.toScheme :=
  PiExponentSeshadri.IdealModule.frameOnRange _ j
    (PiExponentSeshadri.IdealModule.frame_restriction L j r hprincipal hregular).some

end PiExponent.ExceptionalAffineChart
end

end OAI
