import OAI.Combinatorics.EditApproximation.Geometry.LocalSeedSchedule
import OAI.Combinatorics.EditApproximation.Probability.AdaptiveSeedTrace
import OAI.Combinatorics.EditApproximation.Geometry.LocalSeedSequence

namespace OAI

/-! Extract the actual per-pass streams from a finite adaptive draw trace.
Earlier-pass streams are preserved when a new draw is appended, and the
lazy program's seed recurrence is exactly the trace's returned table. -/

namespace EditApproximation

theorem localSeedSequence_streams_congr {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
    (source target : List α) (N P F exponent H Q T S copies : ℕ)
    (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
    (group group' : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer integer' : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ →
      TargetInterval target.length → ℕ)
    (initial : PhysicalEntry M J target.length → ℕ) (pass : ℕ)
    (hgroup : ∀ p < pass, group p = group' p)
    (hinteger : ∀ p < pass, integer p = integer' p) :
    localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass =
      localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group' integer' initial pass := by
  induction pass with
  | zero => rfl
  | succ pass ih =>
    have hprev := ih (fun p hp => hgroup p (by omega)) (fun p hp => hinteger p (by omega))
    simp only [localSeedSequence, hprev, localPassValue, hgroup pass (by omega), hinteger pass (by omega)]

section Trace

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

abbrev LocalScheduledTrace (passes : ℕ) := AdaptiveSeedTrace Seed
  (LocalScheduledSeedDraw (R := R) source target N P T H) passes

noncomputable def localTraceSeed (passes : ℕ)
    (trace : LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes) : Seed :=
  adaptiveTraceValue (localScheduledSeedNext (R := R) source target N P T S H) passes trace

theorem localTraceSeed_succ (passes : ℕ)
    (trace : LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H (passes + 1)) :
    localTraceSeed source target N P T S H (passes + 1) trace =
      localScheduledSeedNext source target N P T S H passes
        (localTraceSeed source target N P T S H passes trace.1)
        (trace.2 (localTraceSeed source target N P T S H passes trace.1)) := rfl

def localTraceInitial : (passes : ℕ) → LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes → Seed
  | 0, seed => seed
  | passes + 1, trace => localTraceInitial passes trace.1

noncomputable def localTraceGroup : (passes : ℕ) →
    LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes →
    ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M ell (ell ^ 80)
  | 0, _ => fun _ _ _ _ _ _ _ _ => 0
  | passes + 1, trace => fun pass copy node time =>
    if pass = passes then
      if hcopy : copy < H ^ 2 then
        physicalRawGroupDraws M J N target.length thetaExponent ell (ell ^ 80) R
          (fun key => trace.2 (localTraceSeed source target N P T S H passes trace.1)
            ⟨copy, hcopy⟩ (.inr key)) node time
      else fun _ _ _ _ => 0
    else localTraceGroup passes trace.1 pass copy node time

noncomputable def localTraceInteger : (passes : ℕ) →
    LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes →
    ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ
  | 0, _ => fun _ _ _ _ _ _ => 0
  | passes + 1, trace => fun pass copy =>
    if pass = passes then
      if hcopy : copy < H ^ 2 then
        physicalRawOnlineIntegers source target
          (clampedSeedNat (localTraceSeed source target N P T S H passes trace.1))
          N P ell (scheduledSeedFactor N passes) T thetaExponent H tau
          (fun key => trace.2 (localTraceSeed source target N P T S H passes trace.1)
            ⟨copy, hcopy⟩ (.inl key))
      else fun _ _ _ _ => 0
    else localTraceInteger passes trace.1 pass copy

theorem localTraceGroup_before (passes : ℕ)
    (trace : LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H (passes + 1))
    (pass : ℕ) (hpass : pass < passes) :
    localTraceGroup source target N P T S H (passes + 1) trace pass =
      localTraceGroup source target N P T S H passes trace.1 pass := by
  funext copy node time
  simp only [localTraceGroup, ite_eq_right (show pass ≠ passes by omega)]

theorem localTraceInteger_before (passes : ℕ)
    (trace : LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H (passes + 1))
    (pass : ℕ) (hpass : pass < passes) :
    localTraceInteger source target N P T S H (passes + 1) trace pass =
      localTraceInteger source target N P T S H passes trace.1 pass := by
  funext copy
  simp only [localTraceInteger, ite_eq_right (show pass ≠ passes by omega)]

theorem localTracePassValue (passes : ℕ)
    (trace : LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H (passes + 1))
    (copy : Fin (H ^ 2)) (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length) :
    localPassValue source target N P ell thetaExponent H (ell ^ 80) T
      (scheduledSeedFactor N) tau eta kappa delta
      (localTraceGroup source target N P T S H (passes + 1) trace)
      (localTraceInteger source target N P T S H (passes + 1) trace)
      (clampedSeedNat (localTraceSeed source target N P T S H passes trace.1))
      passes copy.val node t q =
    physicalLocalJointValue source target
      (clampedSeedNat (localTraceSeed source target N P T S H passes trace.1))
      N P ell (scheduledSeedFactor N passes) T thetaExponent H (ell ^ 80) tau eta kappa delta
      (trace.2 (localTraceSeed source target N P T S H passes trace.1) copy) node t q := by
  simp only [localPassValue, localTraceGroup, localTraceInteger, ite_true, dite_eq_left copy.isLt,
    physicalLocalJointValue]

theorem localTraceSeed_eq : ∀ (passes : ℕ)
    (trace : LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes),
    localSeedSequence source target N P ell thetaExponent H (ell ^ 80) T S (H ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
      (localTraceGroup source target N P T S H passes trace)
      (localTraceInteger source target N P T S H passes trace)
      (clampedSeedNat (localTraceInitial source target N P T H passes trace)) passes =
    clampedSeedNat (localTraceSeed source target N P T S H passes trace) := by
  intro passes
  induction passes with
  | zero => intro trace; rfl
  | succ passes ih =>
    intro trace
    have hprevious := localSeedSequence_streams_congr source target N P ell thetaExponent H (ell ^ 80)
      T S (H ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
      (localTraceGroup source target N P T S H (passes + 1) trace)
      (localTraceGroup source target N P T S H passes trace.1)
      (localTraceInteger source target N P T S H (passes + 1) trace)
      (localTraceInteger source target N P T S H passes trace.1)
      (clampedSeedNat (localTraceInitial source target N P T H passes trace.1)) passes
      (localTraceGroup_before source target N P T S H passes trace)
      (localTraceInteger_before source target N P T S H passes trace)
    have hseed := hprevious.trans (ih trace.1)
    conv_lhs => rw [localSeedSequence]
    rw [show localTraceInitial source target N P T H (passes + 1) trace =
      localTraceInitial source target N P T H passes trace.1 from rfl]
    rw [hseed]
    rw [localTraceSeed_succ]
    funext state
    change min N (upperMedian (List.ofFn _)) =
      min N (upperMedian (List.ofFn fun copy : Fin (H ^ 2) =>
        ⌈(scheduledSeedMultiplier N passes : ℚ) * physicalLocalJointValue source target
          (clampedSeedNat (localTraceSeed source target N P T S H passes trace.1))
          N P ell (scheduledSeedFactor N passes) T thetaExponent H (ell ^ 80) tau eta kappa delta
          (trace.2 (localTraceSeed source target N P T S H passes trace.1) copy) state.1 S state.2⌉₊))
    apply congrArg (fun values : Fin (H ^ 2) → ℕ => min N (upperMedian (List.ofFn values)))
    funext copy
    rw [localTracePassValue source target N P T S H passes trace copy state.1 S state.2]

theorem localTraceSeed_before (passes : ℕ)
    (trace : LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H (passes + 1)) :
    localSeedSequence source target N P ell thetaExponent H (ell ^ 80) T S (H ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
      (localTraceGroup source target N P T S H (passes + 1) trace)
      (localTraceInteger source target N P T S H (passes + 1) trace)
      (clampedSeedNat (localTraceInitial source target N P T H (passes + 1) trace)) passes =
    clampedSeedNat (localTraceSeed source target N P T S H passes trace.1) := by
  apply (localSeedSequence_streams_congr source target N P ell thetaExponent H (ell ^ 80)
    T S (H ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
    (localTraceGroup source target N P T S H (passes + 1) trace)
    (localTraceGroup source target N P T S H passes trace.1)
    (localTraceInteger source target N P T S H (passes + 1) trace)
    (localTraceInteger source target N P T S H passes trace.1)
    (clampedSeedNat (localTraceInitial source target N P T H passes trace.1)) passes
    (localTraceGroup_before source target N P T S H passes trace)
    (localTraceInteger_before source target N P T S H passes trace)).trans
  exact localTraceSeed_eq source target N P T S H passes trace.1

end Trace

instance localScheduledTrace_measurableSingleton {α : Type*} [DecidableEq α] {M J R : ℕ}
    [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (source target : List α) (N P T H passes : ℕ) :
    MeasurableSingletonClass
      (LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes) := by
  classical
  exact adaptiveSeedTraceSingleton (ClampedPhysicalSeed M J target.length N)
    (LocalScheduledSeedDraw (R := R) source target N P T H) passes

end EditApproximation

end OAI
