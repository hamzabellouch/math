import OAI.Geometry.NodalSets.Charts.SphereWeightedChartL2
import OAI.Geometry.NodalSets.Spectral.SphereWeakResolvent

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section
local instance sphereCompletedGreenTestMeasurable : MeasurableSpace Base := borel Base
local instance sphereCompletedGreenTestBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_completed_green_test (d : SphereEnergyData) (v : SphereEnergySmooth d)
    (g : Base → ℝ) (hg : Continuous g)
    (hgreen : ∀ u : SphereEnergySmooth d,
      sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v) =
        -(∫ x, (SphereEnergySmooth.toSmooth d u : Base → ℝ) x*g x ∂sphereReferenceMeasure))
    (z : SphereEnergyHilbert d) :
    sphereCompletedDirichlet d z (sphereEnergyToCompletion d v) =
      -inner ℝ (sphereEnergyL2Map d z)
        (sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le)
          (fun x ↦ g x/d.density x) (hg.div d.continuous (fun x ↦ (d.positive x).ne'))) := by
  let G := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le)
    (fun x ↦ g x/d.density x) (hg.div d.continuous (fun x ↦ (d.positive x).ne'))
  change sphereCompletedDirichlet d z (sphereEnergyToCompletion d v) = -inner ℝ (sphereEnergyL2Map d z) G
  apply (sphereEnergyToCompletion_dense d).induction_on
    (p := fun z ↦ sphereCompletedDirichlet d z (sphereEnergyToCompletion d v) =
      -inner ℝ (sphereEnergyL2Map d z) G) z
  · apply isClosed_eq
    · exact (continuous_id.inner continuous_const).sub
        ((sphereEnergyL2Map d).continuous.inner continuous_const)
    · exact ((sphereEnergyL2Map d).continuous.inner continuous_const).neg
  · intro u
    rw [sphereCompletedDirichlet_coe,hgreen,sphereEnergyL2Map_coe]
    change -(∫ x, (SphereEnergySmooth.toSmooth d u : Base → ℝ) x*g x ∂sphereReferenceMeasure) =
      -inner ℝ (sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le)
        (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous) G
    rw [sphereWeightedToLp_inner]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x ↦ by
      change _ = d.density x*(SphereEnergySmooth.toSmooth d u : Base → ℝ) x*(g x/d.density x)
      field_simp [(d.positive x).ne'])

end
end Yau.Target

end OAI
