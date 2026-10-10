import OAI.Combinatorics.LowSpaceSubsetSum.Search.DecisionRound
import OAI.Combinatorics.LowSpaceSubsetSum.Search.ExactFallback
import OAI.Combinatorics.LowSpaceSubsetSum.Search.MainGuard
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationTaskSpace

namespace OAI

/-! # A uniform input-only finite decision core, including the exact fallback

The threshold is a single constant, independent of the input and of its
polynomial bit-length promise. No solution or mean deficiency enters the
program. The finite sampling law gives one-sided soundness and success
probability at least two thirds.
-/

noncomputable section

namespace LowSpaceSubsetSum

attribute [local instance] Classical.propDecidable

structure DecisionThreshold where
  value : ℕ
  large : 180000000 ≤ value
  halfGap : ∀ n ≥ value, ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
    (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ))

theorem decisionThreshold_exists : Nonempty DecisionThreshold := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp eventually_representation_half_gap
  exact ⟨⟨max N 180000000, le_max_right _ _, fun n hn => hN n (by omega)⟩⟩

/-- A fixed constant can be chosen once for the finite program. -/
def decisionThreshold : DecisionThreshold := Classical.choice decisionThreshold_exists

structure DecisionCore {n : ℕ} (I : Instance n) where
  Outcome : Type
  finite : Fintype Outcome
  law : @FiniteLaw Outcome finite
  accept : Outcome → Bool

namespace DecisionCore

def acceptanceProbability {n : ℕ} {I : Instance n} (D : DecisionCore I) : ℝ :=
  @FiniteLaw.probability D.Outcome D.finite D.law (fun o => D.accept o = true)

end DecisionCore

variable {n : ℕ}

structure CorrectDecisionCore (I : Instance n) where
  core : DecisionCore I
  sound : ∀ o, core.accept o = true → Solvable I
  complete : Solvable I → (2 / 3 : ℝ) ≤ core.acceptanceProbability

def CorrectDecisionCore.ofLaw (I : Instance n) {Ω : Type} [Fintype Ω]
    (law : FiniteLaw Ω) (test : Ω → Bool)
    (hsound : ∀ o, test o = true → Solvable I)
    (hcomplete : Solvable I → (2 / 3 : ℝ) ≤ law.probability (fun o => test o = true)) :
    CorrectDecisionCore I :=
  ⟨⟨Ω, inferInstance, law, test⟩, hsound, hcomplete⟩

def mainDecision (I : Instance n) (hn : 180000000 ≤ n)
    (hs : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ))) : CorrectDecisionCore I :=
  CorrectDecisionCore.ofLaw I ((roundLaw I hn).iid (inputScale I ^ 120))
    (repeatAccept (roundAccept I hn hs (representationBufferCapacity n)))
    (repeated_round_sound I hn hs (representationBufferCapacity n))
    (fun hsolve => (repeated_round_probability I hn hsolve hs hden (representationBufferCapacity n)).le)

def fallbackDecision (I : Instance n) : CorrectDecisionCore I := by
  let D : DecisionCore I :=
    ⟨Unit, inferInstance, FiniteLaw.uniform, fun _ => ExactFallback.decision I⟩
  refine ⟨D, ?_, ?_⟩
  · intro _ hyes
    exact (ExactFallback.decision_correct I).mp hyes
  · intro hsolve
    have he := (ExactFallback.decision_correct I).mpr hsolve
    change (2 / 3 : ℝ) ≤ (FiniteLaw.uniform : FiniteLaw Unit).probability
      (fun _ => ExactFallback.decision I = true)
    simp only [he]
    norm_num [FiniteLaw.probability_true]

def guardedDecision (T : DecisionThreshold) (I : Instance n) : CorrectDecisionCore I :=
  if h : mainGuard T.value n (inputScale I) = true then
    mainDecision I (T.large.trans (of_decide_eq_true h).1)
      (mainGuard_log (by unfold inputScale; omega : 0 < inputScale I) h)
      (T.halfGap n (of_decide_eq_true h).1)
  else fallbackDecision I

theorem guardedDecision_sound (T : DecisionThreshold) (I : Instance n)
    (o : (guardedDecision T I).core.Outcome)
    (hyes : (guardedDecision T I).core.accept o = true) : Solvable I :=
  (guardedDecision T I).sound o hyes

theorem guardedDecision_probability (T : DecisionThreshold) (I : Instance n)
    (hsolve : Solvable I) :
    (2 / 3 : ℝ) ≤ (guardedDecision T I).core.acceptanceProbability :=
  (guardedDecision T I).complete hsolve

theorem guardedDecision_rejects (T : DecisionThreshold) (I : Instance n)
    (hno : ¬ Solvable I) (o : (guardedDecision T I).core.Outcome) :
    (guardedDecision T I).core.accept o = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact hno (guardedDecision_sound T I o h)

end LowSpaceSubsetSum

end

end OAI
