import OAI.NumberTheory.PiExponent.Approximation.FrameSubopens
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections
import OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients

namespace OAI

namespace PiExponentSeshadri.ProjectiveChartSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology Frames
variable {X : Scheme} {U V : X.Opens} (M : X.Modules)
lemma framedSectionsEquiv_restrict (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (s : Γ(M,U)) :
    framedSectionsEquiv V M (restrictOpenFrame h e) (M.presheaf.map (homOfLE h).op s) =
      (X.homOfLE h).appTop (framedSectionsEquiv U M e s) := by
  change (restrictOpenFrame h e).hom.app ⊤
    ((restrictionSectionsIso V M).inv (M.presheaf.map (homOfLE h).op s)) =
    (X.homOfLE h).appTop (e.hom.app ⊤ ((restrictionSectionsIso U M).inv s))
  simp only [restrictOpenFrame, Iso.trans_hom, Iso.symm_hom,
    Scheme.Modules.Hom.comp_app, Iso.app_inv, Iso.app_hom,
    Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    restrictionSectionsIso,
    Scheme.Modules.restrictAppIso]
  let φ := X.homOfLE h
  let W := φ ''ᵁ (⊤ : V.toScheme.Opens)
  let y := (restrictionSectionsIso U M).inv s
  have hn : e.hom.app W ((M.restrict U.ι).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op y) =
      U.toScheme.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (e.hom.app ⊤ y) :=
    CategoryTheory.congr_fun (e.hom.mapPresheaf.naturality (homOfLE (show W ≤ ⊤ from le_top)).op) y
  calc
    _ = (φ.appIso ⊤).hom (e.hom.app W
        ((M.restrict U.ι).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op y)) := by
      change (φ.appIso ⊤).hom (e.hom.app W _) = _
      apply congrArg (φ.appIso ⊤).hom
      apply congrArg (e.hom.app W)
      change (M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _) s =
        (M.presheaf.map _ ≫ M.presheaf.map _) s
      simp only [← Functor.map_comp]
      congr 2
    _ = (φ.appIso ⊤).hom (U.toScheme.presheaf.map
        (homOfLE (show W ≤ ⊤ from le_top)).op (e.hom.app ⊤ y)) := congrArg _ hn
    _ = _ := by
      change (U.toScheme.presheaf.map _ ≫ (φ.appIso ⊤).hom) (e.hom.app ⊤ y) = _
      rw [Scheme.Hom.appIso_hom']
      simp only [φ, Scheme.Hom.appTop, Scheme.homOfLE_app, Scheme.homOfLE_appLE,
        Scheme.Opens.toScheme_presheaf_map]
      erw [← Functor.map_comp]
      congr 2

lemma topIso_hom_restrict (h : V ≤ U) (x : Γ(U.toScheme, ⊤)) :
    V.topIso.hom ((X.homOfLE h).appTop x) =
      X.presheaf.map (homOfLE h).op (U.topIso.hom x) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_hom]
  change (X.presheaf.map _ ≫ X.presheaf.map _) x =
    (X.presheaf.map _ ≫ X.presheaf.map _) x
  erw [← Functor.map_comp, ← Functor.map_comp]
  congr 2

lemma framedCoefficientsEquiv_restrict (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (s : Γ(M,U)) :
    framedCoefficientsEquiv V M (restrictOpenFrame h e)
      (M.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (framedCoefficientsEquiv U M e s) := by
  change V.topIso.hom (framedSectionsEquiv V M (restrictOpenFrame h e)
    (M.presheaf.map (homOfLE h).op s)) =
    X.presheaf.map (homOfLE h).op (U.topIso.hom (framedSectionsEquiv U M e s))
  erw [framedSectionsEquiv_restrict, topIso_hom_restrict]

lemma framedHomCoefficientsEquiv_restrict (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (b : freeOpen X.ringCatSheaf U ⟶ M) :
    framedHomCoefficientsEquiv V M (restrictOpenFrame h e)
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
      X.presheaf.map (homOfLE h).op (framedHomCoefficientsEquiv U M e b) := by
  change framedCoefficientsEquiv V M (restrictOpenFrame h e)
    (freeOpenEquiv X.ringCatSheaf M V
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b)) =
    X.presheaf.map (homOfLE h).op
      (framedCoefficientsEquiv U M e (freeOpenEquiv X.ringCatSheaf M U b))
  erw [freeOpenEquiv_naturality]
  exact framedCoefficientsEquiv_restrict M h e _

end
end PiExponentSeshadri.ProjectiveChartSections

end OAI
