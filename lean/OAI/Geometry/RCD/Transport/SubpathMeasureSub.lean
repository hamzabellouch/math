import OAI.Geometry.RCD.Transport.OptimalMidpointSplice

namespace OAI

/-! # Removing a finite subplan commutes with restriction of time -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem subpath_map_sub (π κ : Measure C(Time,X)) [IsFiniteMeasure κ]
    (hκ : κ≤π) (s t : Time) :
    (π-κ).map (subpath s t)=π.map (subpath s t)-κ.map (subpath s t) := by
  ext B hB
  have hm := subpath_measurable (X:=X) s t
  rw [Measure.map_apply hm hB,Measure.sub_apply (hm hB) hκ,
    Measure.sub_apply hB (Measure.map_mono hκ hm),Measure.map_apply hm hB,Measure.map_apply hm hB]

end RegularPointCoordinates

end

end OAI
