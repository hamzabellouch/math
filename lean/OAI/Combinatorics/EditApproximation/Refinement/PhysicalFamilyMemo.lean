import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyOutput
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomMemo
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The finite family is consumed through actual source reads in the shared
memo evaluator. Its final value and law agree with the proved local answer. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Memo

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Family" => PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S



 theorem physicalFamilyMemoResult_value (hP : 0 < P) (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (rootQ : TargetInterval target.length)
    (input : Seed × Family) :
    ((physicalFamilyMemoResult source target N P T S H hH bits encode rootQ input).value : ℝ) =
      physicalFamilyFinalValue source target N P T S H hP rootQ input := by
  unfold physicalFamilyMemoResult
  rw [chargedRandomMemoEvaluate_value source target N P ell exponent H (ell ^ 80) T S
    (passes + 1) (H ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
    (physicalFamilyGroupRead target N P ell exponent H (ell ^ 80) passes (H ^ 2))
    (physicalFamilyOnlineRead target N P ell exponent H (ell ^ 80) passes (H ^ 2))
    (clampedSeedNat input.1)
    (physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes (H ^ 2) input.2)
    (physicalFamilyGroup target N P ell exponent H (ell ^ 80) passes (H ^ 2) input.2)
    (physicalFamilyInteger source target N P ell exponent H (ell ^ 80) T S passes (H ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta hP input.2
      (clampedSeedNat input.1))]
  · rfl
  · exact physicalFamilyGroupRead_value target N P ell exponent H (ell ^ 80) passes (H ^ 2) input.2
  · exact physicalFamilyOnlineRead_value source target N P ell exponent H (ell ^ 80) T S passes (H ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta hP input.2
      (clampedSeedNat input.1)
  · exact hinjective
  · exact hbounded

noncomputable def physicalFamilyMemoAnswer (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (rootQ : TargetInterval target.length) (input : Seed × Family) : ℕ :=
  if source = substring target rootQ.lo rootQ.hi then 0 else
    integerAnswer N ((physicalFamilyMemoResult source target N P T S H hH bits encode rootQ input).value : ℝ)

 theorem physicalFamilyMemoAnswer_eq (hP : 0 < P) (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (rootQ : TargetInterval target.length)
    (input : Seed × Family) :
    physicalFamilyMemoAnswer source target N P T S H hH bits encode rootQ input =
      physicalFamilyFinalAnswer source target N P T S H hP rootQ input := by
  unfold physicalFamilyMemoAnswer physicalFamilyFinalAnswer
  rw [physicalFamilyMemoResult_value source target N P T S H hP hH bits encode hinjective hbounded]

 theorem physicalFamilyMemoAnswer_law (hP : 0 < P) (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (incoming : Measure Seed)
    [IsProbabilityMeasure incoming] (rootQ : TargetInterval target.length) :
    (incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2))).map
        (physicalFamilyMemoAnswer source target N P T S H hH bits encode rootQ) =
    (localFinalProgramLaw (R := R) source target N P T S H incoming).map
        (localFinalProgramAnswer (R := R) source target N P T S H rootQ) := by
  have heq : physicalFamilyMemoAnswer (R := R) source target N P T S H hH bits encode rootQ =
      physicalFamilyFinalAnswer source target N P T S H hP rootQ := by
    funext input
    exact physicalFamilyMemoAnswer_eq source target N P T S H hP hH bits encode hinjective hbounded rootQ input
  rw [heq]
  exact physicalFamilyFinalAnswer_law source target N P T S H hP hH incoming rootQ

end Memo

end EditApproximation

end OAI
