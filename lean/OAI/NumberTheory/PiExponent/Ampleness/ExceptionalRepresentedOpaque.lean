import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedValue

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.IdealPullback
private abbrev schemeFreeOpen (Y : Scheme) (U : Y.Opens) : Y.Modules :=
  freeOpen Y.ringCatSheaf U

variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}
variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme)

theorem exists_representedSectionsOpaque (n : ℕ) :
    ∃ E : (schemeFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) ≃+
      ↥((I^n).map φ), E = representedSectionsEquiv I f j φ hf L ι hL e n :=
  ⟨_, rfl⟩

def representedSectionsOpaque (n : ℕ) :
    (schemeFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) ≃+ ↥((I^n).map φ) :=
  (exists_representedSectionsOpaque I f j φ hf L ι hL e n).choose

theorem representedSectionsOpaque_eq (n : ℕ) :
    representedSectionsOpaque I f j φ hf L ι hL e n =
      representedSectionsEquiv I f j φ hf L ι hL e n :=
  (exists_representedSectionsOpaque I f j φ hf L ι hL e n).choose_spec

theorem representedSectionsOpaque_apply (n : ℕ)
    (b : schemeFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) :
    representedSectionsOpaque I f j φ hf L ι hL e n b =
      representedSectionsEquiv I f j φ hf L ι hL e n b :=
  congrArg (fun E => E b) (representedSectionsOpaque_eq I f j φ hf L ι hL e n)

end
end PiExponent.ExceptionalAffineChart

end OAI
