import OAI.NumberTheory.PiExponent.Approximation.WeightedPullbackDegree
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoefficientBound
import OAI.NumberTheory.PiExponent.Polynomials.WeightedHomogeneousSubstitution

namespace OAI

noncomputable section
namespace PiExponent.WeightedGlobalSectionBound
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.WeightedCompactification PiExponent.WeightedSliceDegree
open PiExponent.AffineJetCoefficientInterface PiExponent.ProjectiveCoefficientBound
variable {K ι σ : Type} [Field K] [Fintype σ]
attribute [local irreducible] Frame Sections AffineJetCoefficientInterface.coefficient
  LineBundle.pullback EventualBound ProjectiveO1.lineBundle
  WeightedCompactification.affineChartMap
  AdmissibleBlowupGeometry.affineChart AdmissibleBlowupGeometry.hyperplane

theorem eventual_supportBound (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (ρ : ι → ℝ) (B : ℝ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B) :
    EventualBound (affineChartMap (R := K) a z hz coordinate hcoordinate)
      (lineBundle (R := K) a) ρ B := by
  let : Nonempty σ := ⟨z⟩
  apply eventual_of_homogeneous (X := Proj (imageGrade (R := K) a))
    (K := K) (ι := ι) (σ := σ) (projectiveMonomialMap (R := K) a)
    (affineChartMap (R := K) a z hz coordinate hcoordinate) ρ B
  intro n e t p hp
  exact WeightedPullbackDegree.pullback_supportBound (K := K) (ι := ι) (σ := σ)
    a z hz coordinate hcoordinate ρ B ha n e t p (hp z)

theorem eventual_admissible_supportBound {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D) :
    EventualBound (AdmissibleBlowupGeometry.affineChart d) (AdmissibleBlowupGeometry.hyperplane d)
      (fun i => (d.curveDegreeWeights i : ℝ)) (AdmissibleBlowupGeometry.scale d).radius := by
  unfold AdmissibleBlowupGeometry.affineChart AdmissibleBlowupGeometry.hyperplane
  exact eventual_supportBound (K := ℂ) (ι := Fin (d.m+1))
    (σ := AdmissibleBlowupGeometry.Index d) (AdmissibleBlowupGeometry.exponents d)
    (AdmissibleBlowupGeometry.constantIndex d)
    ((AdmissibleBlowupGeometry.scale d).exponents_constant d.curveDegreeWeights_pos)
    (AdmissibleBlowupGeometry.coordinateIndex d)
    ((AdmissibleBlowupGeometry.scale d).exponents_coordinate d.curveDegreeWeights_pos)
    (fun i => (d.curveDegreeWeights i : ℝ)) (AdmissibleBlowupGeometry.scale d).radius
    (WeightedHomogeneousSubstitution.admissible_exponent_budget d)

end PiExponent.WeightedGlobalSectionBound
end

end OAI
