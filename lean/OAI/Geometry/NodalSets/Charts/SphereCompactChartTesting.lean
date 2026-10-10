import OAI.Geometry.NodalSets.Charts.SphereChartScalarExtension
import OAI.Geometry.NodalSets.Charts.SphereWeightedChartL2

namespace OAI

namespace Yau.Target
open MeasureTheory
open scoped ContDiff
noncomputable section
local instance sphereCompactChartTestingMeasurable : MeasurableSpace Base := borel Base
local instance sphereCompactChartTestingBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_compact_chart_testing (d : SphereEnergyData) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    ∃ (h : Base → ℝ) (hh : Continuous h), ∀ f : SphereWeightedL2 d,
      Integrable (fun x ↦ f (sphereChartCoordMap p x)*phi x) ∧
      inner ℝ f (sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) h hh) =
        ∫ x, f (sphereChartCoordMap p x)*phi x := by
  have hpc : HasCompactSupport (fun x ↦ phi x/roundCoordDensity x) := by
    convert hc.mul_right (f' := fun x ↦ (roundCoordDensity x)⁻¹) using 1
    rfl
  obtain ⟨F,hF,_,hval⟩ := sphere_chart_scalar_extension p (fun x ↦ phi x/roundCoordDensity x)
    (hp.div roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne')) hpc
  refine ⟨fun x ↦ F x/d.density x,hF.continuous.div d.continuous (fun x ↦ (d.positive x).ne'),?_⟩
  intro f
  have h := sphereWeightedL2_test_chart d f (fun x ↦ F x/d.density x)
    (hF.continuous.div d.continuous (fun x ↦ (d.positive x).ne')) p
  have he : (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)*
      f (sphereChartCoordMap p y)*(F (sphereChartCoordMap p y)/d.density (sphereChartCoordMap p y))) =
      (fun y ↦ f (sphereChartCoordMap p y)*phi y) := by
    funext y
    rw [hval]
    field_simp [(roundCoordDensity_pos y).ne',(d.positive (sphereChartCoordMap p y)).ne']
  rwa [he] at h

end
end Yau.Target

end OAI
