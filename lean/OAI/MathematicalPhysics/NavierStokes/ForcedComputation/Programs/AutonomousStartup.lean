import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StartupClock
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ResidualScaling
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ClassicalUniqueness

namespace OAI

/-!
# Starting an autonomous periodic field from rest

The startup step in §6 of *Universal Computation with Eventually Stationary
Navier–Stokes Forcing*. This proves the analytic transfer for an actual smooth
field, including its material flow. The computational planar processor is a
separate construction, not an assumption hidden in this transfer.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff Topology NNReal
open ShearFlows

namespace ForcedComputation

theorem residual_smooth {V : Velocity} (hV : ContDiff ℝ ∞ V) (ν : ℝ) :
    ContDiff ℝ ∞ (residual ν V) :=
  ((timeDerivative_smooth hV).add ((spatial_fderiv_smooth hV).clm_apply hV)).sub
    ((laplacian_smooth hV).const_smul ν)

theorem residual_solves_NS {V : Velocity} {L : ℝ}
    (hV : ContDiff ℝ ∞ V) (hp : SpatiallyPeriodic L V)
    (hd : Solenoidal V) (h₀ : ∀ x, V (0, x) = 0) (ν : ℝ) :
    IsClassicalSolution L ν (residual ν V) V (fun _ => 0) where
  regularity := smooth_classicalRegularity hV
  periodic_u t _ := hp t
  periodic_p _ _ _ _ := rfl
  pressure_mean _ _ := by simp
  initial := h₀
  divergence_zero t _ := hd t
  equation t ht x := by
    rw [initialTimeDerivative_eq hV ht x, gradient_constant]
    simp only [residual, neg_zero, zero_add]
    abel

theorem ramp_smooth {α : ℝ → ℝ} {W : Space → Space}
    (hα : ContDiff ℝ ∞ α) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (rampVelocity α W) :=
  (hα.comp contDiff_fst).smul (hW.comp contDiff_snd)

theorem ramp_periodic (α : ℝ → ℝ) {W : Space → Space} {L : ℝ}
    (hp : ∀ x n, W (x + latticeVector L n) = W x) :
    SpatiallyPeriodic L (rampVelocity α W) := by
  intro t x n
  simp only [rampVelocity, hp]

theorem ramp_lipschitz {α : ℝ → ℝ} {W : Space → Space} {K : ℝ≥0}
    (hα : ∀ t, |α t| ≤ 1) (hW : LipschitzWith K W) (t : ℝ) :
    LipschitzWith K (fun x => rampVelocity α W (t, x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (rampVelocity α W (t, x)) (rampVelocity α W (t, y)) =
        |α t| * dist (W x) (W y) := by
          simp [rampVelocity, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * dist (W x) (W y) := mul_le_mul_of_nonneg_right (hα t) dist_nonneg
    _ ≤ (K : ℝ) * dist x y := by simpa only [one_mul] using hW.dist_le_mul x y

theorem ramp_materialFlow {L : ℝ} {α : ℝ → ℝ} {W : Space → Space}
    {Φ : ℝ → Space → Space} {K : ℝ≥0}
    (hα : Continuous α) (hαbound : ∀ t, |α t| ≤ 1)
    (hW : LipschitzWith K W)
    (hΦ : IsMaterialFlow L (fun y => W y.2) Φ) :
    IsMaterialFlow L (rampVelocity α W)
      (fun t x => Φ (accumulatedClock α t) x) where
  initial x := by rw [accumulatedClock_zero, hΦ.initial]
  ode t x := (hΦ.ode (accumulatedClock α t) x).scomp t
    (accumulatedClock_hasDerivAt hα t)
  equivariant t x n := hΦ.equivariant _ x n
  unique x γ hγ₀ hγ t := by
    have he : γ = fun t => Φ (accumulatedClock α t) x :=
      ODE_solution_unique_univ (t₀ := 0) (s := fun _ => univ)
        (fun t => (ramp_lipschitz hαbound hW t).lipschitzOnWith)
        (fun t => ⟨hγ t, mem_univ _⟩)
        (fun t => ⟨(hΦ.ode (accumulatedClock α t) x).scomp t
          (accumulatedClock_hasDerivAt hα t), mem_univ _⟩)
        (by simpa only [accumulatedClock_zero, hΦ.initial] using hγ₀)
    exact congrFun he t

theorem startupRamp_abs_le_one (t : ℝ) : |startupRamp t| ≤ 1 := by
  rw [abs_of_nonneg (startupRamp_nonneg t)]
  exact Real.smoothTransition.le_one _

theorem periodic_spatial_lipschitz {L : ℝ} (hL : 0 < L) {W : Space → Space}
    (hW : ContDiff ℝ ∞ W) (hp : ∀ x n, W (x + latticeVector L n) = W x) :
    ∃ K : ℝ≥0, LipschitzWith K W := by
  obtain ⟨K, hK⟩ := smooth_periodic_lipschitz hL (hW.comp contDiff_snd)
    (show SpatiallyPeriodic L (fun y : SpaceTime => W y.2) from fun _ => hp)
    (show TimePeriodic (fun y : SpaceTime => W y.2) from fun _ _ => rfl)
  refine ⟨K, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  simpa using hK.dist_le_mul ((0 : ℝ), x) ((0 : ℝ), y)

/-- The fixed startup preserves every nonnegative-time observation event. -/
theorem startup_materialFlow {L : ℝ} (hL : 0 < L) {W : Space → Space}
    (hW : ContDiff ℝ ∞ W) (hp : ∀ x n, W (x + latticeVector L n) = W x) :
    ∃ Φ : ℝ → Space → Space,
      IsMaterialFlow L (fun y => W y.2) Φ ∧
      IsMaterialFlow L (rampVelocity startupRamp W)
        (fun t x => Φ (accumulatedClock startupRamp t) x) ∧
      ∀ x O, Reaches (fun t => Φ (accumulatedClock startupRamp t) x) O ↔
        Reaches (fun t => Φ t x) O := by
  have hs : ContDiff ℝ ∞ (fun y : SpaceTime => W y.2) := hW.comp contDiff_snd
  have hsp : SpatiallyPeriodic L (fun y : SpaceTime => W y.2) := fun _ => hp
  have htp : TimePeriodic (fun y : SpaceTime => W y.2) := fun _ _ => rfl
  obtain ⟨Φ, hΦ⟩ := smooth_periodic_materialFlow hL hs hsp htp
  obtain ⟨K, hKW⟩ := periodic_spatial_lipschitz hL hW hp
  refine ⟨Φ, hΦ, ramp_materialFlow startupRamp_smooth.continuous
    startupRamp_abs_le_one hKW hΦ, ?_⟩
  intro x O
  exact reaches_comp_iff startupClock_onto (fun t => Φ t x) O

/-- The startup field is a classical forced solution from rest, with a force
which is exactly stationary on the closed interval `[1,∞)`. -/
theorem startup_solution {L : ℝ} {W : Space → Space}
    (hW : ContDiff ℝ ∞ W) (hp : ∀ x n, W (x + latticeVector L n) = W x)
    (hd : ∀ x, divergence W x = 0) (ν : ℝ) :
    ContDiff ℝ ∞ (rampVelocity startupRamp W) ∧
    ContDiff ℝ ∞ (residual ν (rampVelocity startupRamp W)) ∧
    IsClassicalSolution L ν (residual ν (rampVelocity startupRamp W))
      (rampVelocity startupRamp W) (fun _ => 0) ∧
    ∀ t, 1 ≤ t → ∀ x,
      residual ν (rampVelocity startupRamp W) (t, x) =
        advection W x - ν • laplacian W x := by
  have hs := ramp_smooth startupRamp_smooth hW
  exact ⟨hs, residual_smooth hs ν,
    residual_solves_NS hs (ramp_periodic startupRamp hp)
      (ramp_solenoidal startupRamp hd) (ramp_initial_zero startupRamp_zero W) ν,
    fun t ht x => residual_ramp_on_tail ν W (fun _ hs => startupRamp_tail hs) ht
      (startupRamp_smooth.differentiable (by simp) t) x⟩

theorem startup_solution_unique {L ν : ℝ} (hL : 0 < L) (hν : 0 ≤ ν)
    {W : Space → Space} (hW : ContDiff ℝ ∞ W)
    (hp : ∀ x n, W (x + latticeVector L n) = W x)
    (hd : ∀ x, divergence W x = 0) :
    ∀ u p, IsClassicalSolution L ν (residual ν (rampVelocity startupRamp W)) u p →
      ∀ t, 0 ≤ t → ∀ x, u (t, x) = rampVelocity startupRamp W (t, x) ∧ p (t, x) = 0 := by
  have hsol := (startup_solution hW hp hd ν).2.2.1
  obtain ⟨K, hK⟩ := periodic_spatial_lipschitz hL hW hp
  have hb (t : ℝ) (_ : 0 ≤ t) (x : Space) :
      ‖fderiv ℝ (fun y => rampVelocity startupRamp W (t, y)) x‖ ≤ (K : ℝ) :=
    norm_fderiv_le_of_lipschitz ℝ (ramp_lipschitz startupRamp_abs_le_one hK t)
  intro u p hu
  have he := classical_velocity_unique hL hν hu hsol hb
  have hpressure := classical_pressure_unique hL hu hsol he
  exact fun t ht x => ⟨he t ht x, hpressure t ht x⟩

theorem startup_energy_bounded {L : ℝ} (hL : 0 < L) {W : Space → Space}
    (hW : ContDiff ℝ ∞ W) (hp : ∀ x n, W (x + latticeVector L n) = W x) :
    ∃ E : ℝ, ∀ t, kineticEnergy L (rampVelocity startupRamp W) t ≤ E := by
  obtain ⟨B, hB, hb⟩ := periodic_uniform_bound hL (hW.comp contDiff_snd).continuous
    (show SpatiallyPeriodic L (fun y : SpaceTime => W y.2) from fun _ => hp)
    (show TimePeriodic (fun y : SpaceTime => W y.2) from fun _ _ => rfl)
  have hbound (y : SpaceTime) : ‖rampVelocity startupRamp W y‖ ≤ B := by
    calc
      ‖rampVelocity startupRamp W y‖ = |startupRamp y.1| * ‖W y.2‖ := by
        simp only [rampVelocity, norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * ‖W y.2‖ := mul_le_mul_of_nonneg_right (startupRamp_abs_le_one _) (norm_nonneg _)
      _ ≤ B := by simpa only [one_mul, Function.comp_apply] using hb y
  exact ⟨(1 / 2 : ℝ) * volume.real (fundamentalCube L) * (3 * B ^ 2),
    fun t => kineticEnergy_bound (ramp_smooth startupRamp_smooth hW).continuous L hB hbound t⟩

end ForcedComputation

end

end OAI
