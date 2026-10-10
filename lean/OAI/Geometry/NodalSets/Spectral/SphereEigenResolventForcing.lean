import OAI.Geometry.NodalSets.Charts.SphereChartDivergenceData
import OAI.Geometry.NodalSets.Charts.SphereChartWeakDerivative
import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakProduct

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section
local instance sphereEigenForcingMeasurable : MeasurableSpace Base := borel Base
local instance sphereEigenForcingBorel : BorelSpace Base := ⟨rfl⟩

def sphereEigenForcingCoefficient (d : SphereEnergyData) (p : Base) (mu : ℝ)
    (x : Yau.Jets.Coord) : ℝ :=
  (mu⁻¹-1)*(roundCoordDensity x*d.density (sphereChartCoordMap p x))

def sphereEigenForcingDerivative (d : SphereEnergyData) (p : Base) (mu : ℝ)
    (f : SphereWeightedL2 d) (k : Fin 4) (x : Yau.Jets.Coord) : ℝ :=
  sphereEigenForcingCoefficient d p mu x*(sphereChartDerivativeMap d p k (sphereWeakSolution d f)) x+
    Yau.coordPartial (sphereEigenForcingCoefficient d p mu) x k*
      (sphereL2Resolvent d f) (sphereChartCoordMap p x)

theorem sphere_eigen_resolvent_forcing_ae (d : SphereEnergyData) (p : Base)
    (mu : ℝ) (hmu : mu ≠ 0) (f : SphereWeightedL2 d)
    (he : sphereL2Resolvent d f=mu • f) :
    sphereChartResolventForcing d p f =ᵐ[volume]
      (fun x ↦ sphereEigenForcingCoefficient d p mu x*(sphereL2Resolvent d f) (sphereChartCoordMap p x)) := by
  have hpoint : (sphereL2Resolvent d f : Base → ℝ) =ᵐ[sphereWeightedMeasure d.density]
      (fun x ↦ mu*f x) := by
    rw [he]
    exact Lp.coeFn_smul mu f
  have hchart := (sphereWeightedMeasure_ae_chart_iff d p
    (fun y ↦ (sphereL2Resolvent d f) y=mu*f y)).mp hpoint
  filter_upwards [hchart] with x hx
  simp only [sphereChartResolventForcing,sphereEigenForcingCoefficient,hx]
  field_simp

theorem sphere_eigen_resolvent_forcing_H1 (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) (f : SphereWeightedL2 d)
    (he : sphereL2Resolvent d f=mu • f) (k : Fin 4) :
    MemLp (sphereChartResolventForcing d p f) 2 (volume.restrict (realFinCube 4)) ∧
    MemLp (sphereEigenForcingDerivative d p mu f k) 2 (volume.restrict (realFinCube 4)) ∧
    ∀ psi : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realFinCube 4 →
      IntegrableOn (fun x ↦ sphereChartResolventForcing d p f x*Yau.coordPartial psi x k) (realFinCube 4) ∧
      IntegrableOn (fun x ↦ sphereEigenForcingDerivative d p mu f k x*psi x) (realFinCube 4) ∧
      (∫ x in realFinCube 4, sphereChartResolventForcing d p f x*Yau.coordPartial psi x k) =
        -(∫ x in realFinCube 4, sphereEigenForcingDerivative d p mu f k x*psi x) := by
  let w := fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)
  have hw : MemLp w 2 (volume.restrict (realFinCube 4)) := by
    obtain ⟨_,_,hb⟩ := sphereWeightedL2_compact_chart_bound d p (realFinCube_isCompact 4)
    exact (hb (sphereL2Resolvent d f)).1
  have ha : ContDiff ℝ ∞ (sphereEigenForcingCoefficient d p mu) :=
    contDiff_const.mul (roundCoordDensity_smooth.mul hrho)
  have hweak : ∀ psi : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realFinCube 4 →
      (∫ x in realFinCube 4, w x*Yau.coordPartial psi x k) =
        -(∫ x in realFinCube 4, (sphereChartDerivativeMap d p k (sphereWeakSolution d f)) x*psi x) := by
    intro psi hp hc hs
    have h := (sphere_chart_weak_derivative d p k (sphereWeakSolution d f) psi hp hc hs).2.2
    change (∫ x in realFinCube 4, (sphereChartDerivativeMap d p k (sphereWeakSolution d f)) x*psi x) =
      -(∫ x in realFinCube 4, w x*Yau.coordPartial psi x k) at h
    linarith only [h]
  have hprod := Yau.real_interior_weak_product (realFinCube_isCompact 4) w
    (sphereChartDerivativeMap d p k (sphereWeakSolution d f)) (sphereEigenForcingCoefficient d p mu)
    hw (Lp.memLp _) ha k hweak
  have hsame : sphereChartResolventForcing d p f =ᵐ[volume.restrict (realFinCube 4)]
      (fun x ↦ sphereEigenForcingCoefficient d p mu x*w x) :=
    ae_restrict_of_ae (sphere_eigen_resolvent_forcing_ae d p mu hmu f he)
  refine ⟨hprod.1.ae_eq hsame.symm,hprod.2.1,fun psi hp hc hs ↦ ?_⟩
  have h := hprod.2.2 psi hp hc hs
  have hi : (fun x ↦ sphereChartResolventForcing d p f x*Yau.coordPartial psi x k) =ᵐ[volume.restrict (realFinCube 4)]
      (fun x ↦ sphereEigenForcingCoefficient d p mu x*w x*Yau.coordPartial psi x k) := by
    filter_upwards [hsame] with x hx
    exact congrArg (fun t : ℝ ↦ t*Yau.coordPartial psi x k) hx
  exact ⟨h.1.congr hi.symm,h.2.1,(integral_congr_ae hi).trans h.2.2⟩

end
end Yau.Target

end OAI
