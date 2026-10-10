import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart
import OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.RestrictionCohomology
open PiExponentSeshadri.IdealPullback


private abbrev schemeFreeOpen (Y : Scheme) (U : Y.Opens) : Y.Modules :=
  freeOpen Y.ringCatSheaf U

section Functions
variable {A B : Type} [CommRing A] [CommRing B] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (h : Spec.map (CommRingCat.ofHom θ) ≫ j = j')

include h in
lemma opensRange_le : j'.opensRange ≤ j.opensRange := by
  change Set.range j' ⊆ Set.range j
  rintro y ⟨b,rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom θ) b, ?_⟩
  exact congr($(h) b)

lemma chart_square :
    j'.isoOpensRange.hom ≫ Y.homOfLE (opensRange_le j j' θ h) =
      Spec.map (CommRingCat.ofHom θ) ≫ j.isoOpensRange.hom := by
  apply (cancel_mono j.opensRange.ι).mp
  simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι, h]

def functionsOnOpenEquiv : Γ(Y,j.opensRange) ≃+* A :=
  j.opensRange.topIso.symm.commRingCatIsoToRingEquiv.trans (chartFunctionsEquiv j)

lemma chartFunctions_naturality (s : Γ(j.opensRange.toScheme,⊤)) :
    chartFunctionsEquiv j' ((Y.homOfLE (opensRange_le j j' θ h)).appTop s) =
      θ (chartFunctionsEquiv j s) := by
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      (j'.isoOpensRange.hom.appTop ((Y.homOfLE (opensRange_le j j' θ h)).appTop s)) =
    θ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom (j.isoOpensRange.hom.appTop s))
  have hc := congrArg (fun g => g.appTop) (chart_square j j' θ h)
  simp only [Scheme.Hom.comp_appTop] at hc
  have he : (Y.homOfLE (opensRange_le j j' θ h)).appTop ≫
        j'.isoOpensRange.hom.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      j.isoOpensRange.hom.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
        CommRingCat.ofHom θ := by
    rw [← Category.assoc, hc, Category.assoc, Scheme.ΓSpecIso_naturality]
  exact CategoryTheory.congr_fun he s

lemma topIso_restriction {U V : Y.Opens} (hUV : U ≤ V) (s : Γ(Y,V)) :
    U.topIso.inv (Y.presheaf.map (homOfLE hUV).op s) =
      (Y.homOfLE hUV).appTop (V.topIso.inv s) := by
  change (Y.presheaf.map (homOfLE hUV).op ≫ U.topIso.inv) s =
    (V.topIso.inv ≫ (Y.homOfLE hUV).appTop) s
  congr 1
  simp only [Scheme.Opens.topIso_inv, Scheme.homOfLE_appTop]
  congr 1
  exact (Y.presheaf.map_comp _ _).symm.trans
    ((congrArg (fun g => Y.presheaf.map g) (Subsingleton.elim _ _)).trans
      (Y.presheaf.map_comp _ _))

lemma functionsOnOpenEquiv_naturality (s : Γ(Y,j.opensRange)) :
    functionsOnOpenEquiv j' (Y.presheaf.map (homOfLE (opensRange_le j j' θ h)).op s) =
      θ (functionsOnOpenEquiv j s) := by
  change chartFunctionsEquiv j' (j'.opensRange.topIso.inv
    (Y.presheaf.map (homOfLE (opensRange_le j j' θ h)).op s)) =
      θ (chartFunctionsEquiv j (j.opensRange.topIso.inv s))
  rw [topIso_restriction]
  exact chartFunctions_naturality j j' θ h _

end Functions

variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}

theorem restrictedInclusion_value (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
    (U : Y.Opens) (s : Γ(L.sheaf, U)) :
    (PiExponentSeshadri.InvertibleLocal.restrictedInclusion L ι U.ι).app ⊤
      ((restrictionSectionsIso U L.sheaf).inv s) = U.topIso.inv (ι.app U s) := by
  change (U.ι.appIso ⊤).hom
    (ι.app (U.ι ''ᵁ ⊤) (L.sheaf.presheaf.map (eqToHom U.ι_image_top).op s)) = _
  rw [Scheme.Opens.ι_appIso]
  change ι.app (U.ι ''ᵁ ⊤) (L.sheaf.presheaf.map (eqToHom U.ι_image_top).op s) =
    Y.presheaf.map (eqToHom U.ι_image_top).op (ι.app U s)
  exact CategoryTheory.congr_fun (ι.mapPresheaf.naturality (eqToHom U.ι_image_top).op) s

variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme)

def sectionsOnOpenEquiv (n : ℕ) :
    Γ((L.pow n).sheaf, j.opensRange) ≃+ ↥((I^n).map φ) :=
  (restrictionSectionsIso (chartOpen j).1 (L.pow n).sheaf).addCommGroupIsoToAddEquiv.symm.trans
    (sectionsEquiv I f j φ hf L ι hL e n)

theorem sectionsOnOpenEquiv_apply (n : ℕ) (s : Γ((L.pow n).sheaf, j.opensRange)) :
    (sectionsOnOpenEquiv I f j φ hf L ι hL e n s).val =
      chartFunctionsEquiv j ((chartOpen j).1.topIso.inv
        ((idealPowerInclusion L ι n).app j.opensRange s)) := by
  change (sectionsEquiv I f j φ hf L ι hL e n
    ((restrictionSectionsIso (chartOpen j).1 (L.pow n).sheaf).inv s)).val = _
  erw [sectionsEquiv_apply]
  exact congrArg (chartFunctionsEquiv j)
    (restrictedInclusion_value (L.pow n) (idealPowerInclusion L ι n) (chartOpen j).1 s)

def representedSectionsEquiv (n : ℕ) :
    (schemeFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) ≃+ ↥((I^n).map φ) :=
  ({ freeOpenEquiv Y.ringCatSheaf (L.pow n).sheaf j.opensRange with
      map_add' := fun _ _ => rfl } :
      (schemeFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) ≃+
        Γ((L.pow n).sheaf, j.opensRange)).trans
    (sectionsOnOpenEquiv I f j φ hf L ι hL e n)

variable {B : Type} [CommRing B]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (h : Spec.map (CommRingCat.ofHom θ) ≫ j = j')
  (φ' : R →+* B) (hf' : j' ≫ f = Spec.map (CommRingCat.ofHom φ'))
  (e' : L.sheaf.restrict (chartOpen j').1.ι ≅ O (chartOpen j').1.toScheme)

theorem sectionsOnOpenEquiv_restrict (n : ℕ) (s : Γ((L.pow n).sheaf, j.opensRange)) :
    (sectionsOnOpenEquiv I f j' φ' hf' L ι hL e' n
      ((L.pow n).sheaf.presheaf.map (homOfLE (opensRange_le j j' θ h)).op s)).val =
      θ (sectionsOnOpenEquiv I f j φ hf L ι hL e n s).val := by
  rw [sectionsOnOpenEquiv_apply, sectionsOnOpenEquiv_apply]
  have hn := CategoryTheory.congr_fun
    ((idealPowerInclusion L ι n).mapPresheaf.naturality
      (homOfLE (opensRange_le j j' θ h)).op) s
  change (idealPowerInclusion L ι n).app j'.opensRange
      ((L.pow n).sheaf.presheaf.map (homOfLE (opensRange_le j j' θ h)).op s) =
    Y.presheaf.map (homOfLE (opensRange_le j j' θ h)).op
      ((idealPowerInclusion L ι n).app j.opensRange s) at hn
  rw [hn]
  exact functionsOnOpenEquiv_naturality j j' θ h _

theorem representedSectionsEquiv_restrict (n : ℕ)
    (s : schemeFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) :
    (representedSectionsEquiv I f j' φ' hf' L ι hL e' n
      (freeOpenMap Y.ringCatSheaf (homOfLE (opensRange_le j j' θ h)) ≫ s)).val =
      θ (representedSectionsEquiv I f j φ hf L ι hL e n s).val := by
  change (sectionsOnOpenEquiv I f j' φ' hf' L ι hL e' n
    (freeOpenEquiv Y.ringCatSheaf (L.pow n).sheaf j'.opensRange
      (freeOpenMap Y.ringCatSheaf (homOfLE (opensRange_le j j' θ h)) ≫ s))).val = _
  erw [freeOpenEquiv_naturality]
  exact sectionsOnOpenEquiv_restrict I f j φ hf L ι hL e j' θ h φ' hf' e' n _

end
end PiExponent.ExceptionalAffineChart

end OAI
