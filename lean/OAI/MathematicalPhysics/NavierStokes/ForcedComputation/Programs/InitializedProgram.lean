import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Velocity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StationaryBounds

namespace OAI

/-! A single loading period followed by the machine's periodic shear program. -/

noncomputable section
open Set
open scoped ContDiff
open ShearFlows

namespace ForcedComputation

def hasTimeCollar (c : ℝ) (V : Velocity) : Prop :=
  ∀ t, |t - c| < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0

def collarSwitch (c : ℝ) (U V : Velocity) : Velocity :=
  letI := ShearFlows.oneTwentyEightAtLeastTwo
  letI := ShearFlows.twoAtLeastTwo
  fun y =>
  (1 - Real.smoothTransition (128 * (y.1 - c) + 1 / 2)) • U y +
    Real.smoothTransition (128 * (y.1 - c) + 1 / 2) • V y

theorem collarSwitch_smooth (c : ℝ) {U V : Velocity}
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (collarSwitch c U V) := by
  have hχ : ContDiff ℝ ∞ (fun y : SpaceTime =>
      Real.smoothTransition (128 * (y.1 - c) + 1 / 2)) :=
    Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (contDiff_fst.sub contDiff_const)).add contDiff_const)
  exact ((contDiff_const.sub hχ).smul hU).add (hχ.smul hV)

theorem collarSwitch_before {c : ℝ} {U V : Velocity}
    (hU : hasTimeCollar c U) (hV : hasTimeCollar c V)
    {t : ℝ} (ht : t ≤ c) (x : Space) : collarSwitch c U V (t, x) = U (t, x) := by
  by_cases hχ : 128 * (t - c) + 1 / 2 ≤ 0
  · simp only [collarSwitch, Real.smoothTransition.zero_of_nonpos hχ,
      sub_zero, one_smul, zero_smul, add_zero]
  · have hc : |t - c| < (1 / 32 : ℝ) := by
      apply abs_lt.mpr
      constructor <;> linarith
    simp only [collarSwitch, hU t hc x, hV t hc x, smul_zero, add_zero]

theorem collarSwitch_after {c : ℝ} {U V : Velocity}
    (hU : hasTimeCollar c U) (hV : hasTimeCollar c V)
    {t : ℝ} (ht : c ≤ t) (x : Space) : collarSwitch c U V (t, x) = V (t, x) := by
  by_cases hχ : 1 ≤ 128 * (t - c) + 1 / 2
  · simp only [collarSwitch, Real.smoothTransition.one_of_one_le hχ,
      sub_self, one_smul, zero_smul, zero_add]
  · have hc : |t - c| < (1 / 32 : ℝ) := by
      apply abs_lt.mpr
      constructor <;> linarith
    simp only [collarSwitch, hU t hc x, hV t hc x, smul_zero, add_zero]

theorem collarSwitch_periodic {L c : ℝ} {U V : Velocity}
    (hU : SpatiallyPeriodic L U) (hV : SpatiallyPeriodic L V) :
    SpatiallyPeriodic L (collarSwitch c U V) := by
  intro t x n
  simp only [collarSwitch, hU t x n, hV t x n]

def initializedProgram (loader body : Input) : Velocity :=
  collarSwitch 1 (collarSwitch 0 (fun _ => 0) loader.realizingVelocity)
    body.realizingVelocity

private theorem loader_collar_zero (loader : Input) :
    hasTimeCollar 0 loader.realizingVelocity := by
  intro t ht x
  exact realizingVelocity_vanish_near_integers loader 0 (by simpa using ht) x

private theorem loader_started_collar_one (loader : Input) :
    hasTimeCollar 1 (collarSwitch 0 (fun _ => 0) loader.realizingVelocity) := by
  intro t ht x
  have hp : 0 ≤ t := by have h := (abs_lt.mp ht).1; linarith
  rw [collarSwitch_after (fun _ _ _ => rfl) (loader_collar_zero loader) hp]
  exact realizingVelocity_vanish_near_integers loader 1 (by simpa using ht) x

private theorem body_collar_one (body : Input) :
    hasTimeCollar 1 body.realizingVelocity := by
  intro t ht x
  exact realizingVelocity_vanish_near_integers body 1 (by simpa using ht) x

theorem initializedProgram_before (loader body : Input) {t : ℝ} (ht : t ≤ 0) (x : Space) :
    initializedProgram loader body (t, x) = 0 := by
  rw [initializedProgram, collarSwitch_before (loader_started_collar_one loader)
    (body_collar_one body) (by linarith)]
  exact collarSwitch_before (fun _ _ _ => rfl) (loader_collar_zero loader) ht x

theorem initializedProgram_loading (loader body : Input) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : Space) :
    initializedProgram loader body (t, x) = loader.realizingVelocity (t, x) := by
  rw [initializedProgram, collarSwitch_before (loader_started_collar_one loader)
    (body_collar_one body) ht.2]
  exact collarSwitch_after (fun _ _ _ => rfl) (loader_collar_zero loader) ht.1 x

theorem initializedProgram_tail (loader body : Input) {t : ℝ} (ht : 1 ≤ t) (x : Space) :
    initializedProgram loader body (t, x) = body.realizingVelocity (t, x) :=
  collarSwitch_after (loader_started_collar_one loader) (body_collar_one body) ht x

theorem initializedProgram_smooth {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body) :
    ContDiff ℝ ∞ (initializedProgram loader body) :=
  collarSwitch_smooth 1
    (collarSwitch_smooth 0 contDiff_const (realizingVelocity_smooth hloader))
    (realizingVelocity_smooth hbody)

theorem initializedProgram_periodic {loader body : Input}
    (hperiod : loader.period = body.period) :
    SpatiallyPeriodic body.period (initializedProgram loader body) := by
  apply collarSwitch_periodic
  · apply collarSwitch_periodic
    · intro _ _ _; rfl
    · rw [← hperiod]
      exact realizingVelocity_spatially_periodic loader
  · exact realizingVelocity_spatially_periodic body

theorem initializedProgram_bounded {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body)
    (hperiod : loader.period = body.period) :
    BoundedMixedDerivatives (initializedProgram loader body) :=
  boundedMixed_of_stationary_tail (by exact_mod_cast hbody.period_pos)
    (initializedProgram_smooth hloader hbody) (realizingVelocity_smooth hbody)
    (initializedProgram_periodic hperiod) (realizingVelocity_spatially_periodic body)
    (realizingVelocity_time_periodic body)
    (fun _ ht x => initializedProgram_before loader body ht.le x)
    (fun _ ht x => initializedProgram_tail loader body ht.le x)

end ForcedComputation

end

end OAI
