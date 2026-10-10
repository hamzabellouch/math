import OAI.Combinatorics.EditApproximation.Geometry.LocalCommonTrace
import OAI.Combinatorics.EditApproximation.Geometry.LocalTraceMemoOutput

namespace OAI

/-! The charged memo answer under one common random source per pass and
one fresh terminal source. Correct marginal laws suffice; hypothetical
seed-indexed draw families are not part of the execution. -/

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
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "cap" => localOnlineMassBound M P H

abbrev LocalCommonTerminalDraw :=
  PhysicalCommonDraw M J N target.length thetaExponent ell (ell ^ 80) R cap

noncomputable def localCommonTerminalLaw :
    Measure (LocalCommonTerminalDraw (M := M) (J := J) (R := R) target N P H) :=
  physicalCommonLaw M J N target.length thetaExponent ell (ell ^ 80) R cap

instance localCommonTerminalLaw_probability : IsProbabilityMeasure
    (localCommonTerminalLaw (M := M) (J := J) (R := R) target N P H) := by
  unfold localCommonTerminalLaw
  infer_instance

noncomputable def localCommonTerminalSample (hP : 0 < P) (seed : Seed)
    (draw : LocalCommonTerminalDraw (M := M) (J := J) (R := R) target N P H) :
    LocalFinalProgramDraw (R := R) source target N P T H seed :=
  physicalCommonSample source target (clampedSeedNat seed) N P ell
    (scheduledSeedFactor N passes) T thetaExponent H (ell ^ 80) R cap tau
    (physicalLocalOnlineMass_le source target (clampedSeedNat seed) N P ell
      (scheduledSeedFactor N passes) T thetaExponent H tau hP) draw

omit [NeZero R] in
theorem localCommonTerminalSample_law (hP : 0 < P) (seed : Seed) :
    (localCommonTerminalLaw (M := M) (J := J) (R := R) target N P H).map
        (localCommonTerminalSample source target N P T H hP seed) =
      localFinalProgramDrawLaw (R := R) source target N P T H seed :=
  physicalCommonSample_law source target (clampedSeedNat seed) N P ell
    (scheduledSeedFactor N passes) T thetaExponent H (ell ^ 80) R cap tau
    (physicalLocalOnlineMass_le source target (clampedSeedNat seed) N P ell
      (scheduledSeedFactor N passes) T thetaExponent H tau hP)

abbrev LocalCommonFinalOutcome :=
  LocalCommonTrace (M := M) (J := J) (R := R) target N P H passes ×
    LocalCommonTerminalDraw (M := M) (J := J) (R := R) target N P H

noncomputable def localCommonFinalLaw (incoming : Measure Seed) :
    Measure (LocalCommonFinalOutcome (M := M) (J := J) (R := R) target N P H) :=
  (localCommonTraceLaw (M := M) (J := J) (R := R) target N P H incoming passes).prod
    (localCommonTerminalLaw (M := M) (J := J) (R := R) target N P H)

instance localCommonFinalLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming] :
    IsProbabilityMeasure (localCommonFinalLaw (M := M) (J := J) (R := R) target N P H incoming) := by
  unfold localCommonFinalLaw
  infer_instance

noncomputable def localCommonFinalToTrace (hP : 0 < P)
    (outcome : LocalCommonFinalOutcome (M := M) (J := J) (R := R) target N P H) :
    LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H :=
  (localCommonToScheduled source target N P T H hP passes outcome.1,
    fun seed => localCommonTerminalSample source target N P T H hP seed outcome.2)

noncomputable def localCommonMemoAnswer (hP : 0 < P) (hH : 0 < H)
    (rootQ : TargetInterval target.length)
    (outcome : LocalCommonFinalOutcome (M := M) (J := J) (R := R) target N P H) : ℕ :=
  localTraceMemoAnswer source target N P T S H hH rootQ
    (localCommonFinalToTrace source target N P T H hP outcome)

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem localCommonMemoAnswer_eq (hP : 0 < P) (hH : 0 < H)
    (rootQ : TargetInterval target.length)
    (outcome : LocalCommonFinalOutcome (M := M) (J := J) (R := R) target N P H) :
    localCommonMemoAnswer source target N P T S H hP hH rootQ outcome =
      localFinalProgramAnswer (R := R) source target N P T S H rootQ
        (localCommonSeed source target N P T S H hP passes outcome.1,
          fun seed => localCommonTerminalSample source target N P T H hP seed outcome.2) := by
  rw [localCommonMemoAnswer, localTraceMemoAnswer_eq]
  unfold localTraceFinalProjection localCommonFinalToTrace
  rw [localCommonToScheduled_seed]

theorem localCommonMemoAnswer_law (hP : 0 < P) (hH : 0 < H)
    (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (rootQ : TargetInterval target.length) :
    (localCommonFinalLaw (M := M) (J := J) (R := R) target N P H incoming).map
        (localCommonMemoAnswer source target N P T S H hP hH rootQ) =
      (localFinalProgramLaw (R := R) source target N P T S H incoming).map
        (localFinalProgramAnswer (R := R) source target N P T S H rootQ) := by
  classical
  let reindex := Prod.map (localCommonSeed (M := M) (J := J) (R := R) source target N P T S H hP passes)
    (id : LocalCommonTerminalDraw (M := M) (J := J) (R := R) target N P H → _)
  let answer : Seed × LocalCommonTerminalDraw (M := M) (J := J) (R := R) target N P H → ℕ :=
    fun pair => localFinalProgramAnswer (R := R) source target N P T S H rootQ
      (pair.1, fun seed => localCommonTerminalSample source target N P T H hP seed pair.2)
  have hanswer : localCommonMemoAnswer (R := R) source target N P T S H hP hH rootQ =
      answer ∘ reindex := by
    funext outcome
    exact localCommonMemoAnswer_eq source target N P T S H hP hH rootQ outcome
  have hproduct :
      (localCommonFinalLaw (M := M) (J := J) (R := R) target N P H incoming).map reindex =
        (localScheduledSeedLaw (R := R) source target N P T S H incoming passes).prod
          (localCommonTerminalLaw (M := M) (J := J) (R := R) target N P H) := by
    unfold localCommonFinalLaw
    rw [show reindex = Prod.map (localCommonSeed (M := M) (J := J) (R := R) source target N P T S H hP passes) id from rfl]
    rw [← Measure.map_prod_map _ _ (measurable_of_finite _) measurable_id,
      Measure.map_id, localCommonSeed_law]
  rw [hanswer, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _), hproduct]
  unfold localFinalProgramLaw
  change _ = (Measure.map (fun pair : LocalFinalProgramOutcome
    (M := M) (J := J) (R := R) source target N P T H =>
    if source = substring target rootQ.lo rootQ.hi then 0 else
      integerAnswer N (localFinalProgramValue (R := R) source target N P T S H rootQ
        pair.1 (pair.2 pair.1))) _)
  convert (adaptiveAnswerLaw_eq_of_marginals
    (localFinalProgramDrawLaw (R := R) source target N P T H)
    (localCommonTerminalLaw (M := M) (J := J) (R := R) target N P H)
    (localCommonTerminalSample source target N P T H hP)
    (localCommonTerminalSample_law source target N P T H hP)
    (localScheduledSeedLaw (R := R) source target N P T S H incoming passes)
    (fun seed draw => if source = substring target rootQ.lo rootQ.hi then 0 else
      integerAnswer N (localFinalProgramValue (R := R) source target N P T S H rootQ seed draw))) using 1
  · rfl

theorem localCommonMemoAnswer_event (hP : 0 < P) (hH : 0 < H)
    (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (rootQ : TargetInterval target.length) (event : Set ℕ) :
    (localCommonFinalLaw (M := M) (J := J) (R := R) target N P H incoming).real
      {outcome | localCommonMemoAnswer source target N P T S H hP hH rootQ outcome ∈ event} =
    (localFinalProgramLaw (R := R) source target N P T S H incoming).real
      {outcome | localFinalProgramAnswer (R := R) source target N P T S H rootQ outcome ∈ event} := by
  classical
  have h := congrArg (fun law : Measure ℕ => law.real event)
    (localCommonMemoAnswer_law (R := R) source target N P T S H hP hH incoming rootQ)
  simpa only [map_measureReal_apply (measurable_of_finite _) (Set.to_countable _).measurableSet,
    Set.preimage] using h

end Output

end EditApproximation

end OAI
