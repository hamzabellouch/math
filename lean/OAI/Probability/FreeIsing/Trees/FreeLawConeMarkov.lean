import OAI.Probability.FreeIsing.Conditioning.Descent
import OAI.Probability.FreeIsing.Estimates.FreeIsingMeasure
import OAI.Probability.FreeIsing.Trees.BroadcastConeMarkov

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367
open RootedBroadcast

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
local instance (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  infer_instance

theorem HasFreeIsingLaw.condIndepFun_outside_cone_given_parent {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (b : TreeVertex d) (hb : b.val ≠ []) :
    CondIndepFun (isingSpinMeasurable.comap (fun x => x (parent b)))
      (measurable_pi_apply (parent b)).comap_le
      (fun x => fun v : OutsideConeVertex b => x v.val)
      (fun x => fun v : DescendantVertex b => x v.val) μ := by
  have hp : MeasurePreserving (factor theta) (labelMeasure d) μ :=
    ⟨measurable_factor d theta, (hμ.eq_freeIsingMeasure h0 h1).symm⟩
  apply condIndepFun_of_comp_measurePreserving (labelMeasure d) μ (factor theta) hp
    (isingSpinMeasurable.comap (fun x => x (parent b)))
    (measurable_pi_apply (parent b)).comap_le (by fun_prop) (by fun_prop)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using
    RootedBroadcast.condIndepFun_outside_cone_given_parent theta b hb

theorem HasFreeIsingLaw.condIndepFun_outside_cone_given_child {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (b : TreeVertex d) (hb : b.val ≠ []) :
    CondIndepFun (isingSpinMeasurable.comap (fun x => x b))
      (measurable_pi_apply b).comap_le
      (fun x => fun v : OutsideConeVertex b => x v.val)
      (fun x => fun v : DescendantVertex b => x v.val) μ := by
  have hp : MeasurePreserving (factor theta) (labelMeasure d) μ :=
    ⟨measurable_factor d theta, (hμ.eq_freeIsingMeasure h0 h1).symm⟩
  apply condIndepFun_of_comp_measurePreserving (labelMeasure d) μ (factor theta) hp
    (isingSpinMeasurable.comap (fun x => x b))
    (measurable_pi_apply b).comap_le (by fun_prop) (by fun_prop)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using
    RootedBroadcast.condIndepFun_outside_cone_given_child theta b hb

end Problem367

end

end OAI
