import OAI.MathematicalPhysics.NavierStokes.Material.Plateaus
import OAI.MathematicalPhysics.NavierStokes.Material.Scheduling

namespace OAI

namespace Alternating
open scoped Topology BigOperators
open Memory

noncomputable section

def velocitySlot (I : MachineInput) : ℕ → Space → Space
  | 0 => loadingVelocity I
  | n + 1 => slotVelocity I.1 I.2.length n

theorem velocitySlot_smooth (I : MachineInput) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (velocitySlot I n) := by
  cases n with
  | zero => exact loadingVelocity_smooth I
  | succ n => exact slotVelocity_smooth I.1 I.2.length n

theorem velocitySlot_divergence (I : MachineInput) (n : ℕ) (x : Space) :
    divergence (velocitySlot I n) x = 0 := by
  cases n with
  | zero => exact loadingVelocity_divergence I x
  | succ n => exact slotVelocity_divergence I.1 I.2.length n x

theorem velocitySlot_support (I : MachineInput) (n : ℕ) :
    tsupport (velocitySlot I n) ⊆ Metric.closedBall 0 3 := by
  cases n with
  | zero => exact loadingVelocity_support I
  | succ n => exact slotVelocity_support I.1 I.2.length n

def constructedVelocity (I : MachineInput) : Field :=
  shiftedSum (deriv clock) (velocitySlot I)

theorem constructedVelocity_contDiff (I : MachineInput) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (constructedVelocity I)) :=
  shiftedSum_smooth clock_pulse_smooth (fun _ => clock_pulse_nonpos)
    (velocitySlot I) (velocitySlot_smooth I)

theorem constructedVelocity_smooth (I : MachineInput) : SmoothUpToZero (constructedVelocity I) :=
  (constructedVelocity_contDiff I).contDiffOn

theorem constructedVelocity_support (I : MachineInput) :
    SupportedIn (Metric.closedBall 0 3) (constructedVelocity I) := by
  apply shiftedSum_supported
  intro n x hx
  exact notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (velocitySlot_support I n h)) |>.self_of_nhds

theorem constructedVelocity_divergence (I : MachineInput) (t : ℝ) (x : Space) :
    divergence (constructedVelocity I t) x = 0 :=
  shiftedSum_divergence (fun _ => clock_pulse_nonpos) (velocitySlot I)
    (fun n => (velocitySlot_smooth I n).differentiable (by simp)) (velocitySlot_divergence I) t x

theorem constructedVelocity_initial_zero (I : MachineInput) (x : Space) :
    constructedVelocity I 0 x = 0 :=
  shiftedSum_zero (fun _ => clock_pulse_nonpos) (velocitySlot I) le_rfl x

def trajectoryNode (I : MachineInput) (hI : ValidInput I) : ℕ → Space
  | 0 => observedParticle
  | n + 1 => snapshot I hI n

def trajectoryDelta (I : MachineInput) (hI : ValidInput I) (n : ℕ) : Space :=
  trajectoryNode I hI (n + 1) - trajectoryNode I hI n

def constructedTrajectory (I : MachineInput) (hI : ValidInput I) (t : ℝ) : Space :=
  observedParticle + progressSum (trajectoryDelta I hI) t

theorem constructedTrajectory_on_slot (I : MachineInput) (hI : ValidInput I) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (n : ℝ) (n + 1)) :
    constructedTrajectory I hI t = trajectoryNode I hI n + clock (t - n) • trajectoryDelta I hI n := by
  rw [constructedTrajectory, progressSum_on_slot _ n ht]
  have htelescope : ∑ j ∈ Finset.range n, trajectoryDelta I hI j =
      trajectoryNode I hI n - observedParticle := Finset.sum_range_sub (trajectoryNode I hI) n
  rw [htelescope]
  abel

theorem constructedTrajectory_at_nat (I : MachineInput) (hI : ValidInput I) (n : ℕ) :
    constructedTrajectory I hI (n : ℝ) = trajectoryNode I hI n := by
  rw [constructedTrajectory_on_slot I hI n ⟨le_rfl, by linarith⟩,
    sub_self, clock_nonpos le_rfl, zero_smul, add_zero]

theorem trajectory_interpolation (I : MachineInput) (hI : ValidInput I) (n : ℕ) (u : ℝ) :
    trajectoryNode I hI (n + 1) + u • trajectoryDelta I hI (n + 1) = slotPoint I hI n u := by
  simp only [trajectoryNode, trajectoryDelta, slotPoint]
  module

theorem trajectory_loading (I : MachineInput) (hI : ValidInput I) (u : ℝ) :
    trajectoryNode I hI 0 + u • trajectoryDelta I hI 0 = loadingPoint I u := by
  simp [trajectoryDelta, trajectoryNode, loadingPoint, loadingDisplacement_eq I hI]

theorem velocitySlot_on_trajectory (I : MachineInput) (hI : ValidInput I) (n : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) :
    velocitySlot I n (trajectoryNode I hI n + u • trajectoryDelta I hI n) = trajectoryDelta I hI n := by
  cases n with
  | zero =>
    rw [velocitySlot, trajectory_loading I hI u,
      loadingVelocity_on_plateau I (loadingPoint_norm_lt I hI hu), loadingDisplacement_eq I hI]
    rfl
  | succ n =>
    rw [velocitySlot, trajectory_interpolation, slotVelocity_at_slotPoint I hI n hu]
    rfl

theorem nonnegative_in_slot {t : ℝ} (ht : 0 ≤ t) :
    ∃ n : ℕ, t ∈ Set.Icc (n : ℝ) (n + 1) :=
  ⟨⌊t⌋₊, Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩

theorem constructedTrajectory_hasDerivAt (I : MachineInput) (hI : ValidInput I) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivAt (constructedTrajectory I hI)
      (constructedVelocity I t (constructedTrajectory I hI t)) t := by
  obtain ⟨n, hn⟩ := nonnegative_in_slot ht
  have hder := (progressSum_hasDerivAt (trajectoryDelta I hI) t).const_add observedParticle
  rw [pulseSum_on_slot _ n hn] at hder
  change HasDerivAt (constructedTrajectory I hI) _ t at hder
  change HasDerivAt (constructedTrajectory I hI)
    (shiftedSum (deriv clock) (velocitySlot I) t (constructedTrajectory I hI t)) t
  rw [pulseSum_on_slot _ n hn, constructedTrajectory_on_slot I hI n hn,
    velocitySlot_on_trajectory I hI n (clock_mem (t - n))]
  exact hder

theorem constructedTrajectory_solves (I : MachineInput) (hI : ValidInput I) :
    SolvesParticle (constructedVelocity I) observedParticle (constructedTrajectory I hI) := by
  constructor
  · simpa only [Nat.cast_zero, trajectoryNode] using constructedTrajectory_at_nat I hI 0
  · intro t ht
    exact (constructedTrajectory_hasDerivAt I hI ht).hasDerivWithinAt

theorem constructedTrajectory_reaches_iff (I : MachineInput) (hI : ValidInput I) :
    (∃ t : ℝ, 0 ≤ t ∧ 0 < constructedTrajectory I hI t 0) ↔ Halts I := by
  constructor
  · rintro ⟨t, ht, hp⟩
    obtain ⟨n, hn⟩ := nonnegative_in_slot ht
    rw [constructedTrajectory_on_slot I hI n hn] at hp
    cases n with
    | zero =>
      rw [trajectory_loading] at hp
      have hneg := loadingPoint_negative I hI (clock_mem (t - (0 : ℕ)))
      linarith
    | succ n =>
      rw [trajectory_interpolation, slotPoint_coord_zero] at hp
      exact (actualSignal_hit_iff I).1 ⟨n, clock (t - (n + 1 : ℕ)), clock_mem _, hp⟩
  · intro hh
    let n := Nat.find hh
    have hbefore : ∀ j < n, I.1.isHalting (configurationAt I j).state = false := by
      intro j hj
      exact Bool.eq_false_iff.2 (Nat.find_min hh hj)
    have hhalt : I.1.isHalting (configurationAt I n).state = true := Nat.find_spec hh
    refine ⟨(n + 2 : ℕ), by positivity, ?_⟩
    rw [constructedTrajectory_at_nat]
    change snapshot I hI (n + 1) 0 > 0
    simp only [snapshot, memoryPoint_zero]
    rw [signal_first_halt _ _ _ n hbefore hhalt]
    exact epsilon_pos (by have := alphabetBase_ge_four I.1; omega) _ _

theorem explicit_velocity_simulation (I : MachineInput) (hI : ValidInput I) :
    SmoothUpToZero (constructedVelocity I) ∧
    SupportedIn (Metric.closedBall 0 3) (constructedVelocity I) ∧
    (∀ t x, divergence (constructedVelocity I t) x = 0) ∧
    (∀ x, constructedVelocity I 0 x = 0) ∧
    SolvesParticle (constructedVelocity I) observedParticle (constructedTrajectory I hI) ∧
    ((∃ t : ℝ, 0 ≤ t ∧ 0 < constructedTrajectory I hI t 0) ↔ Halts I) :=
  ⟨constructedVelocity_smooth I, constructedVelocity_support I, constructedVelocity_divergence I,
    constructedVelocity_initial_zero I, constructedTrajectory_solves I hI,
    constructedTrajectory_reaches_iff I hI⟩

end
end Alternating

end OAI
