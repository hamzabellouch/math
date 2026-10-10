import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedBody

namespace OAI

/-! A computable time cutoff starts the machine-only periodic body. It changes
only during the final empty part of the preceding period, so the body is
exactly zero before one and exactly periodic from one onward. -/

noncomputable section
namespace ForcedComputation.BalancedBody
open ShearFlows Recorder.Planar PlanarHamiltonian Set
open scoped ContDiff

def activationStart (n : ℕ) : ℚ := 1 - 1 / (4 * ((n : ℚ) + 1))
def activationFinish (n : ℕ) : ℚ := 1 - 1 / (8 * ((n : ℚ) + 1))

theorem activation_intervals (n : ℕ) :
    0 < activationStart n ∧ activationStart n < activationFinish n ∧ activationFinish n < 1 := by
  have hn : (0 : ℚ) < n + 1 := by positivity
  have h₄ : (0 : ℚ) < 4 * (n + 1) := by positivity
  have h₈ : (0 : ℚ) < 8 * (n + 1) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold activationStart
    have h : 1 / (4 * ((n : ℚ) + 1)) < 1 := (div_lt_one h₄).mpr (by nlinarith [Nat.cast_nonneg (α := ℚ) n])
    linarith
  · unfold activationStart activationFinish
    have h : 1 / (8 * ((n : ℚ) + 1)) < 1 / (4 * ((n : ℚ) + 1)) :=
      one_div_lt_one_div_of_lt h₄ (by nlinarith)
    linarith
  · unfold activationFinish
    have h : (0 : ℚ) < 1 / (8 * (n + 1)) := by positivity
    linarith

theorem finish_le_activationStart {n : ℕ} (i : Fin n) :
    PlanarTiming.finish i ≤ activationStart n := by
  have hn : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have hi : (i.val : ℚ) + 1 ≤ n := by exact_mod_cast i.isLt
  unfold PlanarTiming.finish activationStart
  apply (le_sub_iff_add_le).mpr
  apply (mul_le_mul_iff_left₀ (by positivity : (0 : ℚ) < 4 * (n + 1))).mp
  field_simp
  nlinarith

def bodyLength (M : Alternating.Machine) (hM : M.WellFormed) : ℕ :=
  (actions (freshMachine M) (freshInput_valid (BalancedPlanar.referenceValid hM)).1).length

def activation (M : Alternating.Machine) (hM : M.WellFormed) : ℝ → ℝ :=
  smoothRamp (activationStart (bodyLength M hM)) (activationFinish (bodyLength M hM))

def activated (M : Alternating.Machine) (hM : M.WellFormed) : Velocity :=
  fun y => activation M hM y.1 • velocity M hM y

theorem raw_late_zero (M : Alternating.Machine) (hM : M.WellFormed) {t : ℝ}
    (ht : t ∈ Icc (activationStart (bodyLength M hM) : ℝ) 1) (x : Space) :
    raw M hM (t, x) = 0 := by
  have hn := activation_intervals (bodyLength M hM)
  have ht0 : 0 ≤ t := (Rat.cast_nonneg.mpr hn.1.le).trans ht.1
  have hp : BalancedPlanar.bodyVelocity M hM t (horizontal x) = 0 := by
    rw [show BalancedPlanar.bodyVelocity M hM =
      PlanarHamiltonian.periodicVelocity
        (normalizedPulse (BalancedPlanar.referenceInput M) (BalancedPlanar.referenceValid hM)) from rfl]
    rw [periodicVelocity_on_unit
      (normalizedPulse_valid (BalancedPlanar.referenceInput M) (BalancedPlanar.referenceValid hM))
      (normalizedPulse_inUnit (BalancedPlanar.referenceInput M) (BalancedPlanar.referenceValid hM)) ⟨ht0, ht.2⟩,
      processorVelocity_eq_sum]
    apply Finset.sum_eq_zero
    intro i _
    have hfi : ((normalizedPulse (BalancedPlanar.referenceInput M)
        (BalancedPlanar.referenceValid hM) i).finish : ℝ) ≤ t := by
      exact (Rat.cast_le.mpr (finish_le_activationStart i)).trans ht.1
    have hab := (normalizedPulse_valid (BalancedPlanar.referenceInput M)
      (BalancedPlanar.referenceValid hM) i).2
    rw [Pulse.velocity, smoothPulse_after (by exact_mod_cast hab) hfi, zero_smul]
  simp only [raw, CompactLift.velocity, CompactLift.spatial, VelocityDetector.triangularLift,
    VelocityDetector.horizontalLinear_eq, hp, map_zero, zero_smul, add_zero, smul_zero]

theorem velocity_late_zero (M : Alternating.Machine) (hM : M.WellFormed) {t : ℝ}
    (ht : t ∈ Icc (activationStart (bodyLength M hM) : ℝ) 1) (x : Space) :
    velocity M hM (t, x) = 0 := by
  change BalancedStretch.stretch (raw M hM (t, BalancedStretch.stretch.symm x)) = 0
  rw [raw_late_zero M hM ht, map_zero]

theorem activated_before (M : Alternating.Machine) (hM : M.WellFormed) {t : ℝ}
    (ht : t ≤ 1) (x : Space) : activated M hM (t, x) = 0 := by
  by_cases ha : t ≤ (activationStart (bodyLength M hM) : ℝ)
  · rw [activated, activation, smoothRamp_before
      (by exact_mod_cast (activation_intervals (bodyLength M hM)).2.1) ha, zero_smul]
  · rw [activated, velocity_late_zero M hM ⟨(lt_of_not_ge ha).le, ht⟩, smul_zero]

theorem activated_tail (M : Alternating.Machine) (hM : M.WellFormed) {t : ℝ}
    (ht : 1 ≤ t) (x : Space) : activated M hM (t, x) = velocity M hM (t, x) := by
  rw [activated, activation, smoothRamp_after
    (by exact_mod_cast (activation_intervals (bodyLength M hM)).2.1), one_smul]
  have hfinish : (activationFinish (bodyLength M hM) : ℝ) ≤ 1 := by
    exact_mod_cast (activation_intervals (bodyLength M hM)).2.2.le
  exact hfinish.trans ht

theorem activated_smooth (M : Alternating.Machine) (hM : M.WellFormed) :
    ContDiff ℝ ∞ (activated M hM) :=
  ((smoothRamp_smooth _ _).comp contDiff_fst).smul (velocity_smooth M hM)

theorem activated_support (M : Alternating.Machine) (hM : M.WellFormed) (t : ℝ) :
    tsupport (fun x => activated M hM (t, x)) ⊆ support :=
  (tsupport_smul_subset_right _ _).trans (velocity_support M hM t)

theorem activated_bounded (M : Alternating.Machine) (hM : M.WellFormed) :
    BoundedMixedDerivatives (activated M hM) :=
  boundedMixed_of_compact_tail (activated_smooth M hM) (velocity_smooth M hM)
    support_compact (activated_support M hM) (velocity_support M hM) (velocity_periodic M hM)
    (fun _ ht x => activated_before M hM (by linarith) x)
    (fun _ ht x => activated_tail M hM ht.le x)

end ForcedComputation.BalancedBody

end

end OAI
