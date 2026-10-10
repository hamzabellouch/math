import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFinalAccuracy
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCoarseSeedLaw
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Conditional accuracy of coarse sampling, adaptive median passes and the final fresh query. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory



section Conditional

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H B : ℕ)
  [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : PhysicalEntry M J target.length → ℕ)

noncomputable def wholeFinalAnswer
    (pair : FinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) : ℕ :=
  finalProgramAnswer (R := R) source target N P T S H (finalTargetState target.length) pair

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem wholeFinalAnswer_equal (heq : source = target)
    (pair : FinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) :
    wholeFinalAnswer (R := R) source target N P T S H pair = 0 := by
  apply finalProgramAnswer_equal
  simpa only [finalTargetState, substring, List.take_length, List.drop_zero] using heq

theorem physical_conditional_accuracy (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
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
    (2 / 3 : ℝ) ≤ (finalProgramLaw (R := R) source target N P T S H
      (physicalCoarseSeedLaw source target N B depth)).real
      {pair | EditDistortion.edit source target ≤ wholeFinalAnswer (R := R) source target N P T S H pair ∧
        (wholeFinalAnswer (R := R) source target N P T S H pair : ℝ) ≤
          (1 + epsilon) * EditDistortion.edit source target} := by
  classical
  have hsmall : 256 ≤ (2 : ℕ) ^ 1000 := by
    have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 8 ≤ 1000)
    norm_num only [show (2 : ℕ) ^ 8 = 256 by norm_num] at h
    exact h
  have hcut : 200 ≤ inputSmallLog N := by omega
  have hinitial := physicalCoarseSeedLaw_failure source target N B depth hN hsize hcut
    hB hMeq hJeq hdepth coarseBernstein
  have h := finalProgram_accuracy (R := R) source target N P T S H hN hell hMeq hJeq hPeq
    hTeq hSeq hHeq hsize groupBernstein (physicalCoarseSeedLaw source target N B depth)
    hinitial.le (finalTargetState target.length) epsilon hepsilon haccuracy
  apply (by norm_num : (2 / 3 : ℝ) ≤ 4 / 5).trans
  simpa only [wholeFinalAnswer, stateEditCost, finalTargetState, substring,
    List.take_length, List.drop_zero] using h

end Conditional

end EditApproximation

end OAI
