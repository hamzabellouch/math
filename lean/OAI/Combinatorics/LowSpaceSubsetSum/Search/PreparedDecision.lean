import OAI.Combinatorics.LowSpaceSubsetSum.Search.PreparedDecisionWork
import OAI.Combinatorics.LowSpaceSubsetSum.Search.GuardedDecision

namespace OAI

/-! # Counter-executed decision rounds and their fixed input guard

The repeated procedure uses stored preparation and interrupted trials.
Its finite seed law includes the auxiliary coupling coordinates used in
the success analysis.
-/

noncomputable section
namespace LowSpaceSubsetSum.PreparedDecision

variable {n : ℕ}

abbrev Seed (I : Instance n) (hn : 180000000 ≤ n) :=
  Fin (inputScale I ^ 120) → PreparedDecisionRound.Seed I hn

def run (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (s : Seed I hn) : Bool × ℕ :=
  DecisionRepetition.run
    (PreparedDecisionRound.run I hn (roundLogBudget I (by omega) hscale)) s

def law (I : Instance n) (hn : 180000000 ≤ n) : FiniteLaw (Seed I hn) :=
  (PreparedDecisionRound.law I hn).iid (inputScale I ^ 120)

theorem sound (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (s : Seed I hn) (hy : (run I hn hscale s).1 = true) : Solvable I := by
  rw [run, DecisionRepetition.value] at hy
  exact PreparedDecisionRound.repeated_sound I hn (roundLogBudget I (by omega) hscale) s hy

theorem probability (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ))) (hs : Solvable I) :
    (2 / 3 : ℝ) < (law I hn).probability (fun s => (run I hn hscale s).1 = true) := by
  simp only [run, DecisionRepetition.value, law]
  exact PreparedDecisionRound.repeated_probability I hn (roundLogBudget I (by omega) hscale)
    hs hden hscale

theorem work (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (s : Seed I hn) :
    (run I hn hscale s).2 ≤ inputScale I ^ 622 * 2 ^ ((n + 1) / 2) :=
  PreparedDecisionWork.repeated I hn (roundLogBudget I (by omega) hscale) hscale s

def core (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ))) : CorrectDecisionCore I :=
  CorrectDecisionCore.ofLaw I (law I hn) (fun s => (run I hn hscale s).1)
    (sound I hn hscale) (fun hs => (probability I hn hscale hden hs).le)

def guarded (T : DecisionThreshold) (I : Instance n) : CorrectDecisionCore I :=
  if h : mainGuard T.value n (inputScale I) = true then
    core I (T.large.trans (of_decide_eq_true h).1)
      (mainGuard_log (by unfold inputScale; omega : 0 < inputScale I) h)
      (T.halfGap n (of_decide_eq_true h).1)
  else fallbackDecision I

theorem guarded_sound (T : DecisionThreshold) (I : Instance n)
    (s : (guarded T I).core.Outcome) (hy : (guarded T I).core.accept s = true) : Solvable I :=
  (guarded T I).sound s hy

theorem guarded_probability (T : DecisionThreshold) (I : Instance n) (hs : Solvable I) :
    (2 / 3 : ℝ) ≤ (guarded T I).core.acceptanceProbability :=
  (guarded T I).complete hs

end LowSpaceSubsetSum.PreparedDecision

end

end OAI
