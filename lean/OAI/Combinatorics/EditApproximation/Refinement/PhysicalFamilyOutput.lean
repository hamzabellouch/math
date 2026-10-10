import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilySeedTrace
import OAI.Combinatorics.EditApproximation.Geometry.LocalCommonOutput

namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Output

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ) (hP : 0 < P)

local notation "SeedState" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "Family" => PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)

noncomputable def physicalFamilyFinalValue (rootQ : TargetInterval target.length)
    (input : SeedState × Family) : ℝ :=
  localRequestValue source target N P ell exponent H (ell ^ 80) T S (H ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
    (physicalFamilyGroup target N P ell exponent H (ell ^ 80) passes (H ^ 2) input.2)
    (physicalFamilyInteger source target N P ell exponent H (ell ^ 80) T S passes (H ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta hP input.2
      (clampedSeedNat input.1))
    (clampedSeedNat input.1)
    (PhysicalTableRequest.refinement passes 0
      (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit) T S rootQ)

noncomputable def physicalFamilyFinalAnswer (rootQ : TargetInterval target.length)
    (input : SeedState × Family) : ℕ :=
  if source = substring target rootQ.lo rootQ.hi then 0 else
    integerAnswer N (physicalFamilyFinalValue source target N P T S H hP rootQ input)

 theorem physicalFamily_localPassValue (seed : SeedState) (draw : Family) (pass copy : ℕ)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    localPassValue source target N P ell exponent H (ell ^ 80) T
      (scheduledSeedFactor N) tau eta kappa delta
      (physicalFamilyGroup target N P ell exponent H (ell ^ 80) passes (H ^ 2) draw)
      (physicalFamilyInteger source target N P ell exponent H (ell ^ 80) T S passes (H ^ 2)
        (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta hP draw
        (clampedSeedNat seed))
      (physicalFamilySeed source target N P ell exponent H (ell ^ 80) T S passes (H ^ 2)
        (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta hP draw
        (clampedSeedNat seed) pass) pass copy node t q =
    physicalLocalJointValue source target
      (physicalFamilySeed source target N P ell exponent H (ell ^ 80) T S passes (H ^ 2)
        (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta hP draw
        (clampedSeedNat seed) pass)
      N P ell (scheduledSeedFactor N pass) T exponent H (ell ^ 80) tau eta kappa delta
      (physicalFamilySample source target N P ell exponent H (ell ^ 80) T passes (H ^ 2)
        (scheduledSeedFactor N) tau hP draw
        (physicalFamilySeed source target N P ell exponent H (ell ^ 80) T S passes (H ^ 2)
          (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta hP draw
          (clampedSeedNat seed) pass) pass copy) node t q := rfl

 theorem physicalFamilyFinalValue_eq (rootQ : TargetInterval target.length) (input : SeedState × Family) :
    physicalFamilyFinalValue source target N P T S H hP rootQ input =
      let outcome := physicalFamilyToTrace target N P ell exponent H (ell ^ 80) passes (H ^ 2) input
      localFinalProgramValue source target N P T S H rootQ
        (localCommonSeed source target N P T S H hP passes outcome.1)
        (localCommonTerminalSample source target N P T H hP
          (localCommonSeed source target N P T S H hP passes outcome.1) outcome.2) := by
  rcases input with ⟨seed, draw⟩
  dsimp only
  rw [physicalFamilyToTrace_fst, physicalFamilyToTrace_snd]
  unfold physicalFamilyFinalValue
  rw [localRequestValue_refinement, physicalFamilySeed_eq, physicalFamily_localPassValue]
  have hseed := physicalFamilySeed_prefix source target N P T S H passes hP draw seed passes le_rfl
  rw [hseed]
  unfold localFinalProgramValue localCommonTerminalSample
  dsimp only [Prod.snd]
  have hs := physicalFamilySample_fin source target N P T H passes hP draw
    (localCommonSeed source target N P T S H hP passes
      (physicalFamilyPrefix target N P H passes draw seed passes le_rfl)) (Fin.last passes) 0
  simp only [Fin.val_last, Fin.val_zero] at hs
  rw [hs]

 theorem physicalFamilyFinalAnswer_eq (hH : 0 < H) (rootQ : TargetInterval target.length)
    (input : SeedState × Family) :
    physicalFamilyFinalAnswer source target N P T S H hP rootQ input =
      localCommonMemoAnswer (M := M) (J := J) (R := R) source target N P T S H hP hH rootQ
        (physicalFamilyToTrace target N P ell exponent H (ell ^ 80) passes (H ^ 2) input) := by
  rw [localCommonMemoAnswer_eq]
  unfold physicalFamilyFinalAnswer localFinalProgramAnswer freshSeedValue
  rw [physicalFamilyFinalValue_eq]

 theorem physicalFamilyFinalAnswer_law (hH : 0 < H) (incoming : Measure SeedState)
    [IsProbabilityMeasure incoming] (rootQ : TargetInterval target.length) :
    (incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2))).map
        (physicalFamilyFinalAnswer source target N P T S H hP rootQ) =
    (localFinalProgramLaw (R := R) source target N P T S H incoming).map
        (localFinalProgramAnswer (R := R) source target N P T S H rootQ) := by
  classical
  let : MeasurableSingletonClass (PhysicalCommonDraw M J N target.length exponent ell
      (ell ^ 80) R (localOnlineMassBound M P H)) := inferInstance
  let := commonSeedTraceFintype SeedState
    (fun _ => LocalCommonDraw (M := M) (J := J) (R := R) target N P H) passes
  let := commonSeedTraceSingleton SeedState
    (fun _ => LocalCommonDraw (M := M) (J := J) (R := R) target N P H) passes
  have heq : physicalFamilyFinalAnswer (R := R) source target N P T S H hP rootQ =
      localCommonMemoAnswer (M := M) (J := J) (R := R) source target N P T S H hP hH rootQ ∘
        physicalFamilyToTrace target N P ell exponent H (ell ^ 80) passes (H ^ 2) := by
    funext input
    exact physicalFamilyFinalAnswer_eq source target N P T S H hP hH rootQ input
  have htrace : (incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2))).map
      (physicalFamilyToTrace target N P ell exponent H (ell ^ 80) passes (H ^ 2)) =
      localCommonFinalLaw (M := M) (J := J) (R := R) target N P H incoming := by
    exact physicalFamilyToTrace_law (Seed := SeedState) (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2) incoming
  rw [heq, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _), htrace]
  exact localCommonMemoAnswer_law source target N P T S H hP hH incoming rootQ

end Output

end EditApproximation

end OAI
