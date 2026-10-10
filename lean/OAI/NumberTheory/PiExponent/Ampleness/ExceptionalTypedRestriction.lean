import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes

namespace OAI

namespace PiExponent.ExceptionalRepresentedTypes
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.IdealPullback
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (h : Spec.map (CommRingCat.ofHom θ) ≫ j = j')

def restrictSections (L : LineBundle Y) (n : ℕ) :
    Sections j L n →+ Sections j' L n where
  toFun b := freeOpenMap Y.ringCatSheaf
    (homOfLE (ExceptionalAffineChart.opensRange_le j j' θ h)) ≫ b
  map_zero' := Limits.HasZeroMorphisms.comp_zero (C := Y.Modules) _ _
  map_add' b c := Preadditive.comp_add _ _ _ _ b c

theorem restrictSections_apply (L : LineBundle Y) (n : ℕ) (b : Sections j L n) :
    restrictSections j j' θ h L n b =
      freeOpenMap Y.ringCatSheaf
        (homOfLE (ExceptionalAffineChart.opensRange_le j j' θ h)) ≫ b := rfl

variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : Frame j L)
  (φ' : R →+* B) (hf' : j' ≫ f = Spec.map (CommRingCat.ofHom φ'))
  (e' : Frame j' L)

theorem representedSectionsTyped_restrict (n : ℕ) (b : Sections j L n) :
    (representedSectionsTyped I f j' φ' hf' L ι hL e' n
      (restrictSections j j' θ h L n b)).val =
      θ (representedSectionsTyped I f j φ hf L ι hL e n b).val := by
  rw [representedSectionsTyped_apply, representedSectionsTyped_apply]
  exact ExceptionalAffineChart.representedSectionsEquiv_restrict
    I f j φ hf L ι hL e j' θ h φ' hf' e' n b

end
end PiExponent.ExceptionalRepresentedTypes

end OAI
