import Mathlib
import OAI.Computability.MinUncut.Machines.RuntimeFinish

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceRuntimeSpace

open Turing Complexity
open scoped BigOperators

attribute [local instance] FinTM2.kFin

def configurationLength (tm : FinTM2) (cfg : tm.Cfg) : Nat :=
  ∑ k : tm.K, (cfg.stk k).length

theorem initial_configurationLength (tm : FinTM2) (input : List (tm.Γ tm.k₀)) :
    configurationLength tm (initList tm input) = input.length := by
  have point (k : tm.K) : ((initList tm input).stk k).length =
      if k = tm.k₀ then input.length else 0 := by
    by_cases h : k = tm.k₀
    · subst k
      simp [initList]
    · simp [initList, h]
  simp [configurationLength, point]

theorem step_configurationLength (tm : FinTM2) (a b : tm.Cfg)
    (transition : tm.step a = some b) :
    configurationLength tm b ≤ configurationLength tm a +
      Fintype.card tm.K * Runtime.programPushBound tm := by
  calc
    _ ≤ ∑ k : tm.K, ((a.stk k).length + Runtime.programPushBound tm) :=
      Finset.sum_le_sum (fun k _ => Runtime.stepStackLength tm k a b transition)
    _ = _ := by simp [configurationLength, Finset.sum_add_distrib]

theorem execution_configurationLength (tm : FinTM2) {start finish : tm.Cfg}
    {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step start (some finish) budget) :
    configurationLength tm finish ≤ configurationLength tm start +
      budget * (Fintype.card tm.K * Runtime.programPushBound tm) :=
  Runtime.executionSizeBound tm.step (configurationLength tm)
    (Fintype.card tm.K * Runtime.programPushBound tm) (step_configurationLength tm) run

theorem prefix_configurationLength (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    {finish : tm.Cfg} {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step (initList tm input) (some finish) budget) :
    configurationLength tm finish ≤ input.length +
      budget * (Fintype.card tm.K * Runtime.programPushBound tm) := by
  simpa only [initial_configurationLength] using execution_configurationLength tm run

noncomputable def spacePolynomial (tm : FinTM2) (time : Polynomial Nat) : Polynomial Nat :=
  Polynomial.X + time * Polynomial.C (Fintype.card tm.K * Runtime.programPushBound tm)

theorem spacePolynomial_eval (tm : FinTM2) (time : Polynomial Nat) (N : Nat) :
    (spacePolynomial tm time).eval N = N +
      time.eval N * (Fintype.card tm.K * Runtime.programPushBound tm) := by
  simp [spacePolynomial]

theorem prefix_length_polynomial (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (time : Polynomial Nat) {finish : tm.Cfg}
    (run : StateTransition.EvalsToInTime tm.step (initList tm input) (some finish)
      (time.eval input.length)) :
    configurationLength tm finish ≤ (spacePolynomial tm time).eval input.length := by
  rw [spacePolynomial_eval]
  exact prefix_configurationLength tm input run

theorem totalLength_eq_configurationLength (tm : FinTM2) (finish : tm.Cfg)
    (base : tm.K → List Bool)
    (sameLengths : ∀ k, (base k).length = (finish.stk k).length) :
    SourceRuntimeFinish.totalLength base = configurationLength tm finish := by
  exact Finset.sum_congr rfl (fun k _ => sameLengths k)

theorem finishCost_le_of_prefix (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    {finish : tm.Cfg} {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step (initList tm input) (some finish) budget)
    (clearKeys : List tm.K) (accumulator output : tm.K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : tm.K → List Bool) (outputEmpty : base output = [])
    (sameLengths : ∀ k, (base k).length = (finish.stk k).length) :
    SourceRuntimeFinish.finishCost clearKeys accumulator base ≤ input.length +
      budget * (Fintype.card tm.K * Runtime.programPushBound tm) + clearKeys.length + 2 := by
  rw [SourceRuntimeFinish.finishCost_eq_totalLength clearKeys accumulator output
    keepAccumulator keepOutput covers base outputEmpty,
    totalLength_eq_configurationLength tm finish base sameLengths]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (prefix_configurationLength tm input run) clearKeys.length) 2

noncomputable def completedTime (tm : FinTM2) (clearKeyCount : Nat)
    (time : Polynomial Nat) : Polynomial Nat :=
  time + spacePolynomial tm time + Polynomial.C (clearKeyCount + 2)

theorem completedTime_eval (tm : FinTM2) (clearKeyCount : Nat)
    (time : Polynomial Nat) (N : Nat) :
    (completedTime tm clearKeyCount time).eval N = time.eval N +
      (N + time.eval N * (Fintype.card tm.K * Runtime.programPushBound tm)) +
      (clearKeyCount + 2) := by
  simp [completedTime, spacePolynomial_eval]

def prefixAndFinishInTime (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (time : Polynomial Nat) {middle finish : tm.Cfg}
    (prefixRun : StateTransition.EvalsToInTime tm.step (initList tm input)
      (some middle) (time.eval input.length))
    (clearKeys : List tm.K) (accumulator output : tm.K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : tm.K → List Bool) (outputEmpty : base output = [])
    (sameLengths : ∀ k, (base k).length = (middle.stk k).length)
    (finishRun : StateTransition.EvalsToInTime tm.step middle (some finish)
      (SourceRuntimeFinish.finishCost clearKeys accumulator base)) :
    StateTransition.EvalsToInTime tm.step (initList tm input) (some finish)
      ((completedTime tm clearKeys.length time).eval input.length) := by
  have joined := StateTransition.EvalsToInTime.trans tm.step _ _ _ _ _ prefixRun finishRun
  have hc := finishCost_le_of_prefix tm input prefixRun clearKeys accumulator output
    keepAccumulator keepOutput covers base outputEmpty sameLengths
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  rw [completedTime_eval]
  omega

end MinUncutGames.Foundations.Hastad.SourceRuntimeSpace

end

end OAI
