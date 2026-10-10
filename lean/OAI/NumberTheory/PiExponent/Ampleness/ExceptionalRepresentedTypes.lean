import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque

namespace OAI

namespace PiExponent.ExceptionalRepresentedTypes
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.IdealPullback
variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}

def Frame (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (L : LineBundle Y) : Type :=
  L.sheaf.restrict (ExceptionalAffineChart.chartOpen j).1.ι ≅
    O (ExceptionalAffineChart.chartOpen j).1.toScheme

def Sections (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (L : LineBundle Y) (n : ℕ) : Type :=
  freeOpen Y.ringCatSheaf j.opensRange ⟶ (L.pow n).sheaf

instance (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (L : LineBundle Y) (n : ℕ) : AddCommGroup (Sections j L n) :=
  Preadditive.homGroup (C := Y.Modules)
    (freeOpen Y.ringCatSheaf j.opensRange) (L.pow n).sheaf

variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : Frame j L)

def representedSectionsTyped (n : ℕ) : Sections j L n ≃+ ↥((I^n).map φ) :=
  ExceptionalAffineChart.representedSectionsOpaque I f j φ hf L ι hL e n

theorem representedSectionsTyped_apply (n : ℕ) (b : Sections j L n) :
    representedSectionsTyped I f j φ hf L ι hL e n b =
      ExceptionalAffineChart.representedSectionsEquiv I f j φ hf L ι hL e n b :=
  ExceptionalAffineChart.representedSectionsOpaque_apply I f j φ hf L ι hL e n b

end
end PiExponent.ExceptionalRepresentedTypes

end OAI
