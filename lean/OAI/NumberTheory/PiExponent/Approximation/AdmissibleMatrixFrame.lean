import OAI.NumberTheory.PiExponent.Ampleness.WeightedAffineFrame
import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleMatrixInterpolation
open AdmissibleBlowupGeometry AlgebraicGeometry CategoryTheory PiExponentSeshadri.Geometry
attribute [local irreducible] WeightedCompactification.lineBundle
  WeightedCompactification.affineChartMap
  AffineJetCoefficientInterface.Frame

theorem frame_exists_of_actual {X : Scheme} {R : Type} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j] (A : LineBundle X)
    (h : Nonempty (A.sheaf.restrict j.opensRange.ι ≅
      structureSheaf j.opensRange.toScheme)) :
    Nonempty (AffineJetCoefficientInterface.Frame j A) := by
  unfold AffineJetCoefficientInterface.Frame
  exact h

theorem monomialFrame_exists {R ι σ : Type} [CommRing R]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Nonempty (AffineJetCoefficientInterface.Frame
      (WeightedCompactification.affineChartMap (R := R) a z hz coordinate hcoordinate)
      (WeightedCompactification.lineBundle (R := R) a)) := by
  exact frame_exists_of_actual
    (X := Proj (WeightedCompactification.imageGrade (R := R) a))
    (R := MvPolynomial ι R)
    (WeightedCompactification.affineChartMap (R := R) a z hz coordinate hcoordinate)
    (WeightedCompactification.lineBundle (R := R) a)
    (WeightedAffineFrame.affineFrame_nonempty (R := R) a z hz coordinate hcoordinate)

theorem actualFrame_exists {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D) :
    Nonempty (AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d)) := by
  exact monomialFrame_exists (R := ℂ)
    (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)
end PiExponent.AdmissibleMatrixInterpolation

end

end OAI
