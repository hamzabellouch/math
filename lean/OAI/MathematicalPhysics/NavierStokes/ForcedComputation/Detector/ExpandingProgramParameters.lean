import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingFiniteExpressions
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingRecorderMass
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingWorkBudget
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NonperiodicForceEvaluation

namespace OAI

/-! Rational program parameters are obtained from a single approximation
to viscosity. The complete address graph, rather than its execution, is
used to compute the source location and the schedule. -/

namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder

def programSigma (C : ℕ) (a : ℕ → ℚ) : ℚ := (C + 1) * (|a 0| + 2)

theorem programSigma_pos (C : ℕ) (a : ℕ → ℚ) : 0 < programSigma C a := by
  unfold programSigma
  positivity

theorem programSigma_budget (C : ℕ) {ν : ℝ} {a : ℕ → ℚ}
    (ha : IsFastRealName a ν) : ν * C ≤ (programSigma C a : ℝ) * 3000 := by
  have happrox : |ν - (a 0 : ℝ)| ≤ 1 := by
    simpa only [errorTolerance, pow_zero, inv_one] using ha 0
  have hν : ν ≤ |(a 0 : ℝ)| + 1 := by
    linarith [(abs_le.mp happrox).2, le_abs_self (a 0 : ℝ)]
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hmul := mul_le_mul_of_nonneg_right hν hC
  simp only [programSigma, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_one, Rat.cast_abs, Rat.cast_ofNat]
  nlinarith [abs_nonneg (a 0 : ℝ)]

def programGrowth (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) : ℚ :=
  2 * (addressGrowth M blank : ℚ) ^ 2

def programFactor (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ) : ℚ :=
  9 * ((addressFactor M blank m : ℚ) + 1) ^ 2

theorem programGrowth_val (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) :
    (programGrowth M blank : ℝ) = workGrowth M blank := by
  simp [programGrowth, workGrowth]

theorem programFactor_val (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ) :
    (programFactor M blank m : ℝ) = workFactor M blank m := by
  simp [programFactor, workFactor]

theorem programGrowth_ge_one (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) : 1 ≤ programGrowth M blank := by
  have h := workGrowth_ge_one M blank
  rw [← programGrowth_val] at h
  exact_mod_cast h

theorem programFactor_nonneg (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ) :
    0 ≤ programFactor M blank m := by
  unfold programFactor
  positivity

def initialCenterCode (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (σ D K : ℚ) : Fin 2 → ℚ :=
  let m := initialWordLength I
  let blank := recorderBlank I.1
  let U := finiteInitializedRecorder I hI
  ![16 * rationalRadius σ D K 0 * (configurationAddress I.1 blank m U).number,
    if haltingControl (finiteMachine I.1 hI.1) U.control then
      16 * rationalRadius σ D K 0 else -(16 * rationalRadius σ D K 0)]

theorem initialCenterCode_val (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (σ D K : ℚ) :
    (fun j => (initialCenterCode I hI σ D K j : ℝ)) =
      configurationCenter I.1 hI.1 (recorderBlank I.1) (initialWordLength I)
        σ D K 0 (finiteInitializedRecorder I hI) := by
  funext j
  cases hc : haltingControl (finiteMachine I.1 hI.1) (finiteInitializedRecorder I hI).control <;>
    fin_cases j <;> simp [initialCenterCode, configurationCenter, rationalRadius_val, hc]

end ForcedComputation.ExpandingDetector

end OAI
