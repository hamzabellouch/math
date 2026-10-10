import OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections
import OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients

namespace OAI

namespace PiExponentSeshadri.ProjectiveChartSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology
open PiExponentSeshadri.FlasqueCohomology FreeOpenUnit Frames


variable {X : Scheme} (U : X.Opens) (M : X.Modules)

theorem freeOpenEquiv_freeTop_comp (b : structureSheaf X ⟶ M) :
    freeOpenEquiv X.ringCatSheaf M ⊤ ((freeTopIso X.ringCatSheaf).hom ≫ b) =
      globalHomEquiv X.ringCatSheaf M b := by
  erw [freeOpenEquiv_comp]
  change b.val.app (op ⊤)
    (freeOpenEquiv X.ringCatSheaf (SheafOfModules.unit X.ringCatSheaf) ⊤
      ((freeOpenEquiv X.ringCatSheaf (SheafOfModules.unit X.ringCatSheaf) ⊤).symm
        (globalHomEquiv X.ringCatSheaf (SheafOfModules.unit X.ringCatSheaf) (𝟙 _)))) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem framedHomCoefficientsEquiv_globalSection
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (b : structureSheaf X ⟶ M) :
    framedHomCoefficientsEquiv U M e
      (freeOpenMap X.ringCatSheaf (homOfLE (show U ≤ ⊤ from le_top)) ≫
        (freeTopIso X.ringCatSheaf).hom ≫ b) =
      U.topIso.hom (coefficient e (restrictSection U.ι b)) := by
  change U.topIso.hom (e.hom.app ⊤ ((restrictionSectionsIso U M).inv
    (freeOpenEquiv X.ringCatSheaf M U
      (freeOpenMap X.ringCatSheaf (homOfLE (show U ≤ ⊤ from le_top)) ≫
        (freeTopIso X.ringCatSheaf).hom ≫ b)))) = _
  erw [freeOpenEquiv_naturality X.ringCatSheaf M
    (homOfLE (show U ≤ ⊤ from le_top)) ((freeTopIso X.ringCatSheaf).hom ≫ b),
    freeOpenEquiv_freeTop_comp]
  apply congrArg U.topIso.hom
  change e.hom.app ⊤
      (M.presheaf.map (eqToHom U.ι_image_top).op
        (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (b.app ⊤ (1 : Γ(X, ⊤))))) =
    e.hom.app ⊤ (b.app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme, ⊤))))
  apply congrArg (e.hom.app ⊤)
  rw [show (U.ι.appIso ⊤).inv (1 : Γ(U.toScheme, ⊤)) =
    (1 : Γ(X, U.ι ''ᵁ ⊤)) from map_one _]
  change (M.presheaf.map _ ≫ M.presheaf.map _) (b.app ⊤ (1 : Γ(X, ⊤))) = _
  rw [← Functor.map_comp]
  rw [show (homOfLE (show U ≤ ⊤ from le_top)).op ≫ (eqToHom U.ι_image_top).op =
    (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op from Subsingleton.elim _ _]
  have hb := CategoryTheory.congr_fun (b.mapPresheaf.naturality
    (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
  change b.app (U.ι ''ᵁ ⊤)
      (X.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op 1) =
    M.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op (b.app ⊤ (1 : Γ(X, ⊤))) at hb
  simpa only [map_one] using hb.symm

end
end PiExponentSeshadri.ProjectiveChartSections

end OAI
