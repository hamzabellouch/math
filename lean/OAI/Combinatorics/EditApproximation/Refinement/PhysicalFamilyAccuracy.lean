import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyMemo
import OAI.Combinatorics.EditApproximation.Geometry.LocalFinalAccuracy

namespace OAI

/-! The finite family is consumed through actual source reads in the shared
memo evaluator. Its final value and law agree with the proved local answer. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Accuracy

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


 theorem physicalFamilyMemoAnswer_event (hP : 0 < P) (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (incoming : Measure Seed)
    [IsProbabilityMeasure incoming] (rootQ : TargetInterval target.length) (event : Set ℕ) :
    (incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2))).real
      {input | physicalFamilyMemoAnswer source target N P T S H hH bits encode rootQ input ∈ event} =
    (localFinalProgramLaw (R := R) source target N P T S H incoming).real
      {input | localFinalProgramAnswer (R := R) source target N P T S H rootQ input ∈ event} := by
  classical
  have h := congrArg (fun law : Measure ℕ => law.real event)
    (physicalFamilyMemoAnswer_law source target N P T S H hP hH bits encode hinjective hbounded incoming rootQ)
  simpa only [map_measureReal_apply (measurable_of_finite _) (Set.to_countable _).measurableSet,
    Set.preimage] using h

variable (B : ℕ) [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : PhysicalEntry M J target.length → ℕ)

/-- Accuracy of the shared source/table memo evaluator under finite Bernstein bounds. -/
 theorem physicalFamilyMemoAnswer_conditional_accuracy (hP : 0 < P) (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
    (hsize : source.length + target.length ≤ N)
    (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
    (hPeq : P = (integerParameters N).P) (hTeq : T = (integerParameters N).T)
    (hSeq : S = (integerParameters N).S) (hHeq : H = inputHeight N)
    (hB : B = (integerParameters N).B)
    (hdepth : ∀ state, depth state = computedCoarseDepth N
      (coarseEntryWidth (physicalSource source state.1) (substring target state.2.lo state.2.hi)))
    (coarseBernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure))
    (groupBernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
      FiniteBernsteinInput (Measure.pi fun _ : Fin
        (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
        (PMF.uniformOfFintype (Fin M)).toMeasure))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (haccuracy : 10 ≤ (inputSmallLog N : ℝ) * epsilon) :
    (2 / 3 : ℝ) ≤ ((physicalCoarseSeedLaw source target N B depth).prod
      (physicalFamilyLaw (M := M) (J := J) (R := R)
        target N P ell exponent H (ell ^ 80) passes (H ^ 2))).real
      {input | EditDistortion.edit source target ≤ physicalFamilyMemoAnswer source target N P T S H
          hH bits encode (finalTargetState target.length) input ∧
        (physicalFamilyMemoAnswer source target N P T S H hH bits encode
          (finalTargetState target.length) input : ℝ) ≤
            (1 + epsilon) * EditDistortion.edit source target} := by
  have hevent := physicalFamilyMemoAnswer_event source target N P T S H hP hH bits encode hinjective hbounded
    (physicalCoarseSeedLaw source target N B depth) (finalTargetState target.length)
    {answer | EditDistortion.edit source target ≤ answer ∧
      (answer : ℝ) ≤ (1 + epsilon) * EditDistortion.edit source target}
  simp only [Set.mem_ofPred_eq] at hevent
  rw [hevent]
  exact local_physical_conditional_accuracy source target N P T S H B depth hN hell hsize
    hMeq hJeq hPeq hTeq hSeq hHeq hB hdepth coarseBernstein groupBernstein epsilon hepsilon haccuracy

end Accuracy

end EditApproximation

end OAI
