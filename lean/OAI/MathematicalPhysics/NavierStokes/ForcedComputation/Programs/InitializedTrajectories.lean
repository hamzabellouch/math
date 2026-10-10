import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InitializedFluid
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.StageFlow

namespace OAI

/-! Exact trajectories of a loader followed by a periodic machine body. -/

noncomputable section
open Set
open ShearFlows

namespace ForcedComputation

theorem initializedFlow_loading {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body)
    {Φ Ψ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow body.period (initializedProgram loader body) Φ)
    (hΨ : IsMaterialFlow loader.period loader.realizingVelocity Ψ)
    (x : Space) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Φ t x = Ψ t x := by
  obtain ⟨K, hK⟩ := initializedProgram_spatial_lipschitz hloader hbody
  apply hΦ.eqOn_of_candidate hK x (fun s => Ψ s x)
    ((continuous_iff_continuousAt.mpr (fun s => (hΨ.ode s x).continuousAt)).continuousOn)
    (by rw [hΨ.initial, hΦ.initial]) ?_ ht
  intro s hs
  rw [initializedProgram_loading loader body ⟨hs.1, hs.2.le⟩]
  exact hΨ.ode s x

theorem initializedFlow_tail {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body)
    {Φ Ψ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow body.period (initializedProgram loader body) Φ)
    (hΨ : IsMaterialFlow body.period body.realizingVelocity Ψ)
    (x : Space) {t : ℝ} (ht : 1 ≤ t) : Φ t x = Ψ (t - 1) (Φ 1 x) := by
  obtain ⟨K, hK⟩ := initializedProgram_spatial_lipschitz hloader hbody
  have hc : Continuous (fun s => Ψ (s - 1) (Φ 1 x)) :=
    (continuous_iff_continuousAt.mpr (fun s => (hΨ.ode s (Φ 1 x)).continuousAt)).comp
      (continuous_id.sub continuous_const)
  apply hΦ.eqOn_of_candidate hK x (fun s => Ψ (s - 1) (Φ 1 x)) hc.continuousOn
    (by simpa using hΨ.initial (Φ 1 x)) ?_ ⟨ht, le_rfl⟩
  intro s hs
  have hd := (hΨ.ode (s - 1) (Φ 1 x)).scomp s ((hasDerivAt_id s).sub_const 1)
  have hp : body.realizingVelocity (s, Ψ (s - 1) (Φ 1 x)) =
      body.realizingVelocity (s - 1, Ψ (s - 1) (Φ 1 x)) := by
    simpa only [sub_add_cancel] using
      realizingVelocity_time_periodic body (s - 1) (Ψ (s - 1) (Φ 1 x))
  rw [initializedProgram_tail loader body hs.1, hp]
  simpa only [one_smul, Function.comp_def, id_eq] using hd

end ForcedComputation

end

end OAI
