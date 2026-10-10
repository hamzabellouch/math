import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowForce

namespace OAI

/-! After the finite loading interval, the slowed mechanism uses only the
machine's periodic table. This statement concerns the actual force as well. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Filter
open scoped Topology

theorem slow_initialized_tail (loader body : Input) (ν : ℝ)
    {t : ℝ} (ht : Real.exp 1 - 1 ≤ t) (x : Space) :
    slowFromRest (initializedProgram loader body) (t, x) =
      slowVelocity body.realizingVelocity (t, x) ∧
    force ν (slowFromRest (initializedProgram loader body)) (t, x) =
      force ν (slowVelocity body.realizingVelocity) (t, x) := by
  have he : 1 < Real.exp (1 : ℝ) := by
    exact Real.one_lt_exp_iff.mpr (by norm_num)
  have hp : 0 < t := by linarith
  have hlog : (1 : ℝ) ≤ logClock t := by
    apply (Real.le_log_iff_exp_le (show 0 < 1 + t by linarith)).mpr
    linarith
  have hc : ContinuousAt (fun y : SpaceTime => logClock y.1) (t, x) := by
    have hb : ContinuousAt (fun y : SpaceTime => 1 + y.1) (t, x) :=
      continuousAt_const.add continuousAt_fst
    exact (Real.continuousAt_log (by linarith : 1 + t ≠ 0)).comp
      (f := fun y : SpaceTime => 1 + y.1) (x := (t, x)) hb
  have hg : slowFromRest (initializedProgram loader body) =ᶠ[𝓝 (t, x)]
      slowVelocity body.realizingVelocity := by
    filter_upwards [(continuous_fst.tendsto (t, x)).eventually (eventually_gt_nhds hp),
      hc.eventually (eventually_gt_nhds (show 1 - (1 / 32 : ℝ) < logClock t by linarith))]
      with y hy hly
    change (if y.1 ≤ 0 then 0 else (1 + y.1)⁻¹ •
      initializedProgram loader body (logClock y.1, y.2)) =
        (1 + y.1)⁻¹ • body.realizingVelocity (logClock y.1, y.2)
    rw [ite_eq_right (not_le.mpr hy), initializedProgram_tail_extend loader body hly]
  exact ⟨hg.self_of_nhds, force_congr_germ hg ν⟩

end ForcedComputation

end

end OAI
