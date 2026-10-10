import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicSpaceOfPeriodicCurve

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ZeroAtInfty BigOperators

theorem hasDerivAt_of_evaluations {a : ℕ} {F G : ℝ → compatibleJets 2 a}
    (hG : Continuous G)
    (hd : ∀ t X, HasDerivAt (fun s => value (F s) X) (value (G t) X) t) (t : ℝ) :
    HasDerivAt F (G t) t := by
  have he (s : ℝ) : F s = F 0 + ∫ r in (0:ℝ)..s, G r := by
    apply value_injective
    funext X
    change value (F s) X = evaluate X (F 0 + ∫ r in (0:ℝ)..s, G r)
    rw [map_add]
    have hh := (evaluate (a := a) X).intervalIntegral_comp_comm (μ := volume)
      (hG.intervalIntegrable 0 s)
    rw [← hh]
    simp only [evaluate_apply]
    have hc : Continuous (fun r : ℝ => value (G r) X) := (evaluate X).continuous.comp hG
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r X)
      (hc.intervalIntegrable 0 s)]
    ring
  let : SecondCountableTopologyEither ℝ (compatibleJets 2 a) :=
    secondCountableTopologyEither_of_left _ _
  have hh := (intervalIntegral.integral_hasDerivAt_right (E := compatibleJets 2 a)
    (hG.intervalIntegrable 0 t) hG.stronglyMeasurable.stronglyMeasurableAtFilter
    hG.continuousAt).const_add (F 0)
  exact hh.congr_of_eventuallyEq (Eventually.of_forall he)

end VelocityDetection.PeriodicSpace.Jets
end

end OAI
