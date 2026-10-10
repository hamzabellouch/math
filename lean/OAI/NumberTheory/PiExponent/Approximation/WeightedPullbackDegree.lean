import OAI.NumberTheory.PiExponent.Approximation.WeightedFrameDegree
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface
import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame
import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface
import OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialWeightedBound
import OAI.NumberTheory.PiExponent.Polynomials.WeightedHomogeneousSubstitution

namespace OAI

noncomputable section
namespace PiExponent.WeightedPullbackDegree
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
open PiExponent.WeightedCompactification PiExponent.WeightedSliceDegree
open PiExponent.AffineJetPolynomial PiExponent.AffineJetCoefficientFrame
open PiExponent.AffineJetCoefficientInterface
variable {K ι σ : Type} [Field K]
attribute [local irreducible] Frame Sections AffineJetCoefficientInterface.coefficient
  WeightedCompactification.affineChartMap
  AdmissibleBlowupGeometry.affineChart AdmissibleBlowupGeometry.hyperplane
  ProjectiveO1.lineBundle ProjectiveO1.coordinateSection ProjectiveO1.scalars
  ProjectiveO1.coordinateCocycle PiExponentSeshadri.Projective.sectionsMorphism
  PiExponentSeshadri.Projective.CoordinateAtlas.morphism PiExponentSeshadri.Projective.atlasOfFramedSections
  ProjectiveO1.globalSectionChartPolynomial
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.polynomial
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.frame
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.ringEquiv

theorem pullback_supportBound (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (ρ : ι → ℝ) (B : ℝ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B) (n : ℕ)
    (e : Frame (affineChartMap (R := K) a z hz coordinate hcoordinate)
      (lineBundle (R := K) a))
    (s : Sections (ProjectiveO1.lineBundle (R := K) (σ := σ)) n)
    (p : MvPolynomial.homogeneousSubmodule σ K n)
    (hp : dehomogenize z p.val = ProjectiveO1.globalSectionChartPolynomial (R := K) (σ := σ) n z
      (ProjectiveSectionInterface.sectionHom (ProjectiveO1.lineBundle (R := K) (σ := σ)) n s)) :
    SupportBound ρ ((n : ℝ) * B)
      (AffineJetCoefficientInterface.coefficient (affineChartMap (R := K) a z hz coordinate hcoordinate)
        (lineBundle (R := K) a) n e
        (ProjectiveSectionInterface.pullback (ProjectiveO1.lineBundle (R := K) (σ := σ))
          (projectiveMonomialMap (R := K) a) n s)) := by
  let D := ProjectiveIntrinsicCoefficientLaw.intrinsicData (R := K) (σ := σ)
  let ev : MvPolynomial (ChartVariables z) K →+* MvPolynomial ι K :=
    (MvPolynomial.aeval (R := K) (fun j : ChartVariables z =>
      MvPolynomial.monomial (a j.val) (1 : K))).toRingHom
  have hbound : SupportBound ρ ((n : ℝ) * B) (ev (D.polynomial n z (ProjectiveSectionInterface.sectionHom
      (ProjectiveO1.lineBundle (R := K) (σ := σ)) n s))) := by
    dsimp only [D]
    rw [ProjectiveIntrinsicCoefficientLaw.intrinsic_polynomial]
    rw [← hp]
    change SupportBound ρ ((n : ℝ) * B)
      (MvPolynomial.aeval (fun j : ChartVariables z =>
        MvPolynomial.monomial (a j.val) (1 : K)) (dehomogenize z p.val))
    rw [WeightedHomogeneousSubstitution.dehomogenize_substitution a z hz]
    exact WeightedHomogeneousSubstitution.supportBound_substitution ρ B a ha n p
  exact GlobalPolynomialWeightedBound.coefficient_bound
    (X := Proj (imageGrade (R := K) a)) (Y := D.scheme) (K := K) (ι := ι)
    (B := MvPolynomial (ChartVariables z) K)
    (ProjectiveIntrinsicCoefficientLaw.intrinsicBundle (R := K) (σ := σ))
    (projectiveMonomialMap (R := K) a)
    (affineChartMap (R := K) a z hz coordinate hcoordinate)
    (D.chartOpen z) (WeightedChartRingEvaluation.chartFactor (R := K) a z hz coordinate hcoordinate)
    (WeightedChartRingEvaluation.chartFactor_comp (R := K) a z hz coordinate hcoordinate) n
    (D.frame n z) (D.ringEquiv z) (D.polynomial n z)
    (ProjectiveIntrinsicCoefficientLaw.intrinsic_law (R := K) n z) ev
    (by
      intro q
      dsimp only [D]
      rw [ProjectiveIntrinsicCoefficientLaw.intrinsic_ringEquiv]
      exact WeightedChartRingEvaluation.chartFactor_pullback (R := K) a z hz coordinate hcoordinate q)
    ρ ((n : ℝ) * B) e s hbound

end PiExponent.WeightedPullbackDegree
end

end OAI
