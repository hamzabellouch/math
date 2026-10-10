import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.IdealPullback
variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}
variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme)

theorem representedSectionsEquiv_apply (n : ℕ)
    (b : freeOpen Y.ringCatSheaf j.opensRange ⟶ (L.pow n).sheaf) :
    (representedSectionsEquiv I f j φ hf L ι hL e n b).val =
      functionsOnOpenEquiv j
        ((idealPowerInclusion L ι n).app j.opensRange
          (freeOpenEquiv Y.ringCatSheaf (L.pow n).sheaf j.opensRange b)) := by
  exact sectionsOnOpenEquiv_apply I f j φ hf L ι hL e n _

end
end PiExponent.ExceptionalAffineChart

end OAI
