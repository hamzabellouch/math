import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.AddConst
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatContinuous

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile130
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_deriv_at_generator (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => cheegerHeat h s u) (cheegerHeat h t A) t := by
  have hc := cheegerHeat_continuousOn hfin h A
  have hat := (hc t ht.le).continuousAt (Ici_mem_nhds ht)
  have hi : IntervalIntegrable (fun s => cheegerHeat h s A) volume 0 t := (hc.mono (show uIcc (0:ℝ) t ⊆ Ici 0 by rw [uIcc_of_le ht.le]; exact Icc_subset_Ici_self)).intervalIntegrable
  have hd := (intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
      (hc.mono Ioi_subset_Ici_self) t ht) hat).add_const u
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  rw [cheegerHeat_integral_generator hfin h hu hs.le, sub_add_cancel]
end WeakHessian

end
end InlinedFile130

end OAI
