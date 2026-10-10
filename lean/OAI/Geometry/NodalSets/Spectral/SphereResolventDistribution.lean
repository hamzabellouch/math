import OAI.Geometry.NodalSets.Charts.SphereCompactFluxGreen
import OAI.Geometry.NodalSets.Charts.SphereCompletedGreenTest

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section
local instance sphereResolventDistributionMeasurable : MeasurableSpace Base := borel Base
local instance sphereResolventDistributionBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_resolvent_chart_distribution (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (phi : Yau.Jets.Coord → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) :
    let w := sphereL2Resolvent d f
    let D := Yau.weightedDiv roundCoordDensity
      (fun y i ↦ ∑ j, intrinsicRealPrincipal d.tensor p y i j*Yau.coordPartial phi y j)
    Integrable (fun y ↦ roundCoordDensity y*w (sphereChartCoordMap p y)*
      (d.density (sphereChartCoordMap p y)*phi y-D y)) ∧
    Integrable (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)*
      f (sphereChartCoordMap p y)*phi y) ∧
    (∫ y, roundCoordDensity y*w (sphereChartCoordMap p y)*
      (d.density (sphereChartCoordMap p y)*phi y-D y)) =
      ∫ y, roundCoordDensity y*d.density (sphereChartCoordMap p y)*
        f (sphereChartCoordMap p y)*phi y := by
  dsimp only
  let w := sphereL2Resolvent d f
  let D := Yau.weightedDiv roundCoordDensity
    (fun y i ↦ ∑ j, intrinsicRealPrincipal d.tensor p y i j*Yau.coordPartial phi y j)
  obtain ⟨v,g,hv,hg,hval,hgval,hgreen⟩ := sphere_compact_test_divergence_extension
    d.tensor d.smooth d.symm d.pos p phi hphi hc
  let V : SphereEnergySmooth d := ⟨v,hv⟩
  have hgq : Continuous (fun x ↦ g x/d.density x) :=
    hg.continuous.div d.continuous (fun x ↦ (d.positive x).ne')
  let G := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) _ hgq
  obtain ⟨hvi,hve⟩ := sphereWeightedL2_test_chart d w v hv.continuous p
  obtain ⟨hfi,hfe⟩ := sphereWeightedL2_test_chart d f v hv.continuous p
  obtain ⟨hgi,hge⟩ := sphereWeightedL2_test_chart d w _ hgq p
  simp only [hval] at hvi hve hfi hfe
  have heG : (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)*
      w (sphereChartCoordMap p y)*(g (sphereChartCoordMap p y)/d.density (sphereChartCoordMap p y))) =
      (fun y ↦ roundCoordDensity y*w (sphereChartCoordMap p y)*D y) := by
    funext y
    rw [hgval]
    dsimp only [D]
    field_simp [(d.positive (sphereChartCoordMap p y)).ne']
  rw [heG] at hgi hge
  have heS : (fun y ↦ roundCoordDensity y*w (sphereChartCoordMap p y)*
      (d.density (sphereChartCoordMap p y)*phi y-D y)) =
      (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)*w (sphereChartCoordMap p y)*phi y -
        roundCoordDensity y*w (sphereChartCoordMap p y)*D y) := by
    funext y
    ring
  have hweak := sphereWeakSolution_spec d f (sphereEnergyToCompletion d V)
  have hcompleted := sphere_completed_green_test d V g hg.continuous
    (fun u ↦ hgreen (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property)
    (sphereWeakSolution d f)
  rw [sphereCompletedDirichlet,sphereEnergyL2Map_coe] at hcompleted
  rw [sphereEnergyL2Map_coe] at hweak
  change inner ℝ (sphereWeakSolution d f) (sphereEnergyToCompletion d V) -
    inner ℝ w (sphereEnergyL2Linear d V) = -inner ℝ w G at hcompleted
  change inner ℝ w (sphereEnergyL2Linear d V) = _ at hve
  change inner ℝ f (sphereEnergyL2Linear d V) = _ at hfe
  change inner ℝ w G = _ at hge
  change Integrable (fun y ↦ roundCoordDensity y*w (sphereChartCoordMap p y)*
      (d.density (sphereChartCoordMap p y)*phi y-D y)) ∧ _
  rw [heS]
  refine ⟨hvi.sub hgi,hfi,?_⟩
  rw [integral_sub hvi hgi,← hve,← hge,← hfe]
  linarith

end
end Yau.Target

end OAI
