import OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry

namespace OAI

namespace PiExponent.WeightedAffineFrame
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective PiExponentSeshadri.Frames
open PiExponent.WeightedCompactification

theorem frame_nonempty_of_isoOpen_eq {X : Scheme} (M : X.Modules)
    (s : O X ⟶ M) (U : X.Opens) (h : PiExponentSeshadri.SectionOpens.isoOpen s = U) :
    Nonempty (M.restrict U.ι ≅ O U.toScheme) := by
  subst U
  exact ⟨sectionFrame s⟩

variable {R ι σ : Type} [CommRing R]

attribute [local irreducible] WeightedCompactification.lineBundle
  WeightedCompactification.affineChartMap WeightedCompactification.coordinateSection

theorem affineChart_isoOpen (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) a z) =
      (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange := by
  rw [coordinateSection_isoOpen]
  apply TopologicalSpace.Opens.ext
  exact (affineChartMap_range (R := R) a z hz coordinate hcoordinate).symm

theorem affineFrame_nonempty (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Nonempty ((lineBundle (R := R) a).sheaf.restrict
      (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange.ι ≅
        O (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange.toScheme) :=
  frame_nonempty_of_isoOpen_eq (lineBundle (R := R) a).sheaf (coordinateSection (R := R) a z)
    (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange
    (affineChart_isoOpen (R := R) a z hz coordinate hcoordinate)

end
end PiExponent.WeightedAffineFrame

end OAI
