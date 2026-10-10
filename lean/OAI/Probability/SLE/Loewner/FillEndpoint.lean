import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-! Fill a one-sided limit at the initial endpoint of an interval. -/
noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge

theorem continuousOn_fill_endpoint {X : Type*} [TopologicalSpace X]
    {f : ℝ → X} {a : X}
    (hf : ∀ r∈Ioc (0:ℝ) 1, ContinuousAt f r)
    (ha : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 a)) :
    ContinuousOn (fun r : ℝ => if r=0 then a else f r) (Icc 0 1) := by
  intro r hr
  by_cases he : r=0
  · subst r
    have hgt : ContinuousWithinAt (fun r : ℝ => if r=0 then a else f r) (Ioi 0) 0 := by
      change Tendsto _ (𝓝[>] (0:ℝ)) (𝓝 (if (0:ℝ)=0 then a else f 0))
      rw [ite_eq_left rfl]
      apply ha.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (ite_eq_right (ne_of_gt hr)).symm
    exact (continuousWithinAt_Ioi_iff_Ici.mp hgt).mono (fun _ h => h.1)
  · have hp : 0<r := lt_of_le_of_ne hr.1 (Ne.symm he)
    apply ((hf r ⟨hp,hr.2⟩).congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [lt_mem_nhds hp] with s hs
    exact ite_eq_right (ne_of_gt hs)

end SLEExactGauge

end

end OAI
