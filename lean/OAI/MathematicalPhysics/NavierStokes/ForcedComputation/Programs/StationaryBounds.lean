import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ForceMean

namespace OAI

/-!
# Uniform bounds for a smooth startup and its stationary tail

All mixed derivatives are controlled by one compact transition cylinder and
the periodic stationary tail. The argument works with actual germs of the
fields, so it also controls derivatives across the ends of the transition.
-/

noncomputable section
open Set Filter
open scoped ContDiff Topology
open ShearFlows

namespace ForcedComputation

theorem mixedDerivative_eventuallyEq {U V : Velocity} {y : SpaceTime}
    (h : U =ᶠ[𝓝 y] V) (α : List (Fin 4)) :
    mixedDerivative U α =ᶠ[𝓝 y] mixedDerivative V α := by
  induction α with
  | nil => exact h
  | cons j α ih =>
    exact (ih.fderiv (𝕜 := ℝ)).mono (fun z hz => congrArg (fun A => A (spaceTimeDirection j)) hz)

theorem mixedDerivative_zero (α : List (Fin 4)) :
    mixedDerivative (fun _ : SpaceTime => (0 : Space)) α = fun _ => 0 := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    simp only [mixedDerivative, ih, fderiv_fun_const]
    rfl

/-- A smooth periodic field which is zero before zero and stationary after
one has globally bounded derivatives of every mixed order. -/
theorem boundedMixed_of_stationary_tail {L : ℝ} (hL : 0 < L)
    {F G : Velocity} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hpF : SpatiallyPeriodic L F) (hpG : SpatiallyPeriodic L G)
    (htG : TimePeriodic G)
    (hleft : ∀ t, t < 0 → ∀ x, F (t, x) = 0)
    (hright : ∀ t, 1 < t → ∀ x, F (t, x) = G (t, x)) :
    BoundedMixedDerivatives F := by
  intro α
  have hk : IsCompact (Icc (0 : ℝ) 1 ×ˢ fundamentalCube L) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hk.bddAbove_image (mixedDerivative_smooth hF α).continuous.norm.continuousOn
  obtain ⟨D, hD, hbD⟩ := periodic_boundedMixedDerivatives hL hG hpG htG α
  refine ⟨max C D, le_trans hD (le_max_right _ _), ?_⟩
  rintro ⟨t, x⟩
  by_cases ht0 : t < 0
  · have he : F =ᶠ[𝓝 (t, x)] fun _ => 0 := by
      filter_upwards [(continuous_fst.tendsto (t, x)).eventually (eventually_lt_nhds ht0)] with y hy
      exact hleft y.1 hy y.2
    rw [(mixedDerivative_eventuallyEq he α).self_of_nhds, mixedDerivative_zero]
    simpa only [norm_zero] using le_trans hD (le_max_right C D)
  by_cases ht1 : 1 < t
  · have he : F =ᶠ[𝓝 (t, x)] G := by
      filter_upwards [(continuous_fst.tendsto (t, x)).eventually (eventually_gt_nhds ht1)] with y hy
      exact hright y.1 hy y.2
    rw [(mixedDerivative_eventuallyEq he α).self_of_nhds]
    exact (hbD (t, x)).trans (le_max_right _ _)
  · obtain ⟨z, hz, n, hx⟩ := fundamentalCube_representative hL x
    rw [hx, mixedDerivative_spatially_periodic hF hpF]
    exact (hC (mem_image_of_mem _ (show (t, z) ∈ Icc (0 : ℝ) 1 ×ˢ fundamentalCube L from
      ⟨⟨le_of_not_gt ht0, le_of_not_gt ht1⟩, hz⟩))).trans (le_max_left _ _)

theorem residual_spatially_periodic {L : ℝ} {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hp : SpatiallyPeriodic L V) (ν : ℝ) :
    SpatiallyPeriodic L (residual ν V) := by
  intro t x n
  have he : residual ν V (t, x + latticeVector L n) =
      force ν V (t, x + latticeVector L n) + advection (fun y => V (t, y)) (x + latticeVector L n) := by
    unfold residual force
    abel
  rw [he, force_spatially_periodic hV hp]
  unfold residual force advection
  dsimp only
  have hd := CubePeriodic.fderiv (show CubePeriodic L (fun y => V (t, y)) from hp t)
    ((hV.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp))
  rw [hd x n, hp t x n]
  abel

theorem startup_bounds {L : ℝ} (hL : 0 < L) {W : Space → Space}
    (hW : ContDiff ℝ ∞ W) (hp : CubePeriodic L W) (ν : ℝ) :
    BoundedMixedDerivatives (rampVelocity startupRamp W) ∧
      BoundedMixedDerivatives (residual ν (rampVelocity startupRamp W)) := by
  have hU := ramp_smooth startupRamp_smooth hW
  have hpU := ramp_periodic startupRamp hp
  let A : Velocity := fun y => W y.2
  have hA : ContDiff ℝ ∞ A := hW.comp contDiff_snd
  have hpA : SpatiallyPeriodic L A := fun _ => hp
  have htA : TimePeriodic A := fun _ _ => rfl
  have hleft : ∀ t, t < 0 → ∀ x, rampVelocity startupRamp W (t, x) = 0 := by
    intro t ht x
    have ha : startupRamp t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    simp only [rampVelocity, ha, zero_smul]
  have hright : ∀ t, 1 < t → ∀ x, rampVelocity startupRamp W (t, x) = A (t, x) := by
    intro t ht x
    simp only [rampVelocity, startupRamp_tail ht.le, one_smul, A]
  have hFU := residual_smooth hU ν
  have hFA := residual_smooth hA ν
  have hpFU := residual_spatially_periodic hU hpU ν
  have hpFA := residual_spatially_periodic hA hpA ν
  have htFA : TimePeriodic (residual ν A) := by
    intro t x
    have he : residual ν A = fun y => advection W y.2 - ν • laplacian W y.2 := by
      funext y
      simp [residual, A, timeDerivative]
    rw [he]
  refine ⟨boundedMixed_of_stationary_tail hL hU hA hpU hpA htA hleft hright,
    boundedMixed_of_stationary_tail hL hFU hFA hpFU hpFA htFA ?_ ?_⟩
  · intro t ht x
    have ha : startupRamp =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds ht] with s hs
      exact Real.smoothTransition.zero_of_nonpos (by linarith)
    have hd : deriv startupRamp t = 0 :=
      (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ha |>.deriv
    have hz : startupRamp t = 0 := ha.self_of_nhds
    rw [residual_ramp ν startupRamp W (startupRamp_smooth.differentiable (by simp) t), hd, hz]
    simp
  · intro t ht x
    rw [residual_ramp_on_tail ν W (fun _ hs => startupRamp_tail hs) ht.le
      (startupRamp_smooth.differentiable (by simp) t)]
    simp [residual, A, timeDerivative]

end ForcedComputation

end

end OAI
