import OAI.Combinatorics.EditApproximation.Geometry.LocalTraceProgram
import OAI.Combinatorics.EditApproximation.Geometry.LocalFinalAccuracy
import OAI.Combinatorics.EditApproximation.Geometry.ChargedGlobalQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The bounded-key adaptive trace drives the actual charged memo program.
Its final root query has the same distribution as the local answer. The program
uses all previous-pass copies from the trace and one fresh terminal copy. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Output

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "passes" => computedSeedPassCount N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

abbrev LocalTraceFinalOutcome :=
  LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes ×
    (∀ seed : Seed, LocalFinalProgramDraw (R := R) source target N P T H seed)

noncomputable def localTraceAppendFinal
    (outcome : LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H) :
    LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H (passes + 1) :=
  (outcome.1, fun seed _ => outcome.2 seed)



noncomputable def localTraceMemoResult (hH : 0 < H) (rootQ : TargetInterval target.length)
    (outcome : LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H) :=
  let trace := localTraceAppendFinal source target N P T H outcome
  chargedMemoEvaluate source target N P ell thetaExponent H (ell ^ 80) T S (passes + 1) (H ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
    (localTraceGroup source target N P T S H (passes + 1) trace)
    (localTraceInteger source target N P T S H (passes + 1) trace)
    (clampedSeedNat (localTraceInitial source target N P T H passes outcome.1))
    (localFinalRootRequest (M := M) (J := J) target N T S H hH rootQ)

noncomputable def localTraceFinalProjection
    (outcome : LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H) :
    LocalFinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H :=
  (localTraceSeed source target N P T S H passes outcome.1, outcome.2)

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem localTraceMemoResult_value (hH : 0 < H) (rootQ : TargetInterval target.length)
    (outcome : LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H) :
    ((localTraceMemoResult source target N P T S H hH rootQ outcome).value : ℝ) =
      freshSeedValue (localFinalProgramValue (R := R) source target N P T S H rootQ)
        (localTraceFinalProjection source target N P T S H outcome) := by
  let trace := localTraceAppendFinal source target N P T H outcome
  unfold localTraceMemoResult
  rw [chargedMemoEvaluate_value source target N P ell thetaExponent H (ell ^ 80) T S (passes + 1) (H ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
    (localTraceGroup source target N P T S H (passes + 1) trace)
    (localTraceInteger source target N P T S H (passes + 1) trace)
    (clampedSeedNat (localTraceInitial source target N P T H passes outcome.1))
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M))]
  change (localRequestValue source target N P ell thetaExponent H (ell ^ 80) T S (H ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
    (localTraceGroup source target N P T S H (passes + 1) trace)
    (localTraceInteger source target N P T S H (passes + 1) trace)
    (clampedSeedNat (localTraceInitial source target N P T H passes outcome.1))
    (PhysicalTableRequest.refinement passes 0
      (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit) T S rootQ) : ℝ) = _
  rw [localRequestValue_refinement]
  have hseed := localTraceSeed_before source target N P T S H passes trace
  change localSeedSequence source target N P ell thetaExponent H (ell ^ 80) T S (H ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
      (localTraceGroup source target N P T S H (passes + 1) trace)
      (localTraceInteger source target N P T S H (passes + 1) trace)
      (clampedSeedNat (localTraceInitial source target N P T H passes outcome.1)) passes = _ at hseed
  rw [hseed]
  rw [localTracePassValue source target N P T S H passes trace ⟨0, pow_pos hH 2⟩]
  rfl

noncomputable def localTraceMemoAnswer (hH : 0 < H) (rootQ : TargetInterval target.length)
    (outcome : LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H) : ℕ :=
  if source = substring target rootQ.lo rootQ.hi then 0 else
    integerAnswer N ((localTraceMemoResult source target N P T S H hH rootQ outcome).value : ℝ)

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem localTraceMemoAnswer_eq (hH : 0 < H) (rootQ : TargetInterval target.length)
    (outcome : LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H) :
    localTraceMemoAnswer source target N P T S H hH rootQ outcome =
      localFinalProgramAnswer (R := R) source target N P T S H rootQ
        (localTraceFinalProjection source target N P T S H outcome) := by
  unfold localTraceMemoAnswer localFinalProgramAnswer
  rw [localTraceMemoResult_value]

noncomputable def localTraceFinalLaw (incoming : Measure Seed) :
    Measure (LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H) := by
  classical
  exact (adaptiveTraceLaw (localScheduledSeedDrawLaw (M := M) (J := J) (R := R) source target N P T H) incoming passes).prod
    (Measure.pi (localFinalProgramDrawLaw (M := M) (J := J) (R := R) source target N P T H))

instance localTraceFinalLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming] :
    IsProbabilityMeasure (localTraceFinalLaw (R := R) source target N P T H incoming) := by
  unfold localTraceFinalLaw
  infer_instance

theorem localTraceFinalLaw_map (incoming : Measure Seed) :
    (localTraceFinalLaw (R := R) source target N P T H incoming).map
      (localTraceFinalProjection source target N P T S H) =
      localFinalProgramLaw (R := R) source target N P T S H incoming := by
  classical
  have h := Measure.map_prod_map
    (adaptiveTraceLaw (localScheduledSeedDrawLaw (M := M) (J := J) (R := R) source target N P T H) incoming passes)
    (Measure.pi (localFinalProgramDrawLaw (M := M) (J := J) (R := R) source target N P T H))
    (measurable_of_finite (localTraceSeed (M := M) (J := J) (R := R)
      source target N P T S H passes)) measurable_id
  change (localTraceFinalLaw (R := R) source target N P T H incoming).map
    (localTraceFinalProjection source target N P T S H) = _
  rw [localTraceFinalLaw, show localTraceFinalProjection source target N P T S H =
    Prod.map (localTraceSeed source target N P T S H passes) id from rfl]
  rw [← h, Measure.map_id]
  unfold localTraceSeed
  rw [adaptiveTraceLaw_map]
  simp only [localFinalProgramLaw, localScheduledSeedLaw]

theorem localTraceMemoAnswer_event (incoming : Measure Seed) (hH : 0 < H)
    (rootQ : TargetInterval target.length) (event : Set ℕ) :
    (localTraceFinalLaw (R := R) source target N P T H incoming).real
      {outcome | localTraceMemoAnswer source target N P T S H hH rootQ outcome ∈ event} =
      (localFinalProgramLaw (R := R) source target N P T S H incoming).real
        {outcome | localFinalProgramAnswer (R := R) source target N P T S H rootQ outcome ∈ event} := by
  classical
  have h := congrArg
    (fun law : Measure (LocalFinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) =>
      law.real {outcome | localFinalProgramAnswer (R := R) source target N P T S H rootQ outcome ∈ event})
    (localTraceFinalLaw_map (R := R) source target N P T S H incoming)
  rw [map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] at h
  simpa only [Set.preimage, Set.mem_ofPred_eq, localTraceMemoAnswer_eq] using h

end Output

end EditApproximation

end OAI
