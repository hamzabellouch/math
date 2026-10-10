import OAI.Geometry.RCD.Heat.ScaledHeatActionLimit

namespace OAI

/-! # Continuity of each interior slice of an action limit -/

open Set
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

theorem HeatActionLimit.continuous_slice {z : X} (H : HeatActionLimit z)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : Continuous (H.potential t) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hh : ContinuousAt (Function.uncurry H.potential) (t,x) :=
    H.continuous.continuousAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩)
  exact hh.comp (continuous_const.prodMk continuous_id).continuousAt

end RegularPointCoordinates

end OAI
