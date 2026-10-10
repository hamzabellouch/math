import OAI.MathematicalPhysics.Boltzmann.Jets.SpatialDilationAE
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss

namespace OAI

/-! # Time-space dilation preserves spacetime null sets -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.ColdDilationMeasure

theorem spacetime_dilation_quasiMeasurePreserving {r : ℝ} (hr : 0 < r) :
    QuasiMeasurePreserving
      (fun u : ℝ × JetPrototype.Phase => (r*u.1,(r • u.2.1,u.2.2)))
      WeightedLocal.spacetimeVolume WeightedLocal.spacetimeVolume := by
  have ht : QuasiMeasurePreserving (fun t : ℝ => r*t) volume volume :=
    Measure.quasiMeasurePreserving_smul volume hr.ne'
  have hx := spatial_dilation_quasiMeasurePreserving hr
  refine ⟨by fun_prop,?_⟩
  change Measure.map (Prod.map (fun t : ℝ => r*t)
    (fun p : JetPrototype.Phase => (r • p.1,p.2))) _ ≪ _
  rw [← Measure.map_prod_map _ _ ht.measurable hx.measurable]
  exact ht.absolutelyContinuous.prod hx.absolutelyContinuous

end BoltzmannNonuniqueness.ColdDilationMeasure

end

end OAI
