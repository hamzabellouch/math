import OAI.NumberTheory.TwoPoint.Circuits.CircuitSamplingException
import OAI.NumberTheory.TwoPoint.Bounds.CrudeWordCounting

namespace OAI

/-! The sampled gate carries a Boolean certificate for all its errors:
the new single-hit failure test together with the child certificates. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace AC0Circuit

noncomputable def combineGateException {n k s : ℕ}
    (sample : GateSamplingChoices k k s) (c E : Fin k → AC0Circuit n) : AC0Circuit n :=
  certificateDisjunction (fun i : Option (Fin k) => match i with
    | none => gateSamplingException sample c
    | some i => E i)

lemma combineGateException_eval {n k s : ℕ}
    (sample : GateSamplingChoices k k s) (c E : Fin k → AC0Circuit n)
    (x : BooleanCube n) :
    (combineGateException sample c E).eval x = true ↔
      (gateSamplingException sample c).eval x = true ∨ ∃ i, (E i).eval x = true := by
  simp only [combineGateException, certificateDisjunction_eval, Option.exists]

lemma combineGateException_size {n k s : ℕ}
    (sample : GateSamplingChoices k k s) (c E : Fin k → AC0Circuit n) :
    (combineGateException sample c E).size =
      1 + (gateSamplingException sample c).size + ∑ i, (E i).size := by
  simp only [combineGateException, certificateDisjunction_size, Fintype.sum_option]
  omega

lemma combineGateException_depth {n k s d D : ℕ}
    (sample : GateSamplingChoices k k s) (c E : Fin k → AC0Circuit n)
    (hc : ∀ i, (c i).depth ≤ d) (hE : ∀ i, (E i).depth ≤ D)
    (hd : d + 4 ≤ D) :
    (combineGateException sample c E).depth ≤ D + 1 := by
  apply certificateDisjunction_depth
  intro i
  cases i with
  | none => exact (gateSamplingException_depth sample c hc).trans hd
  | some i => exact hE i

end AC0Circuit

theorem exists_certified_and_sample {n k : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (s : ℕ) (c E : Fin k → AC0Circuit n)
    (P : Fin k → BooleanCube n → ℝ) (δ : Fin k → ℝ)
    (hδ : ∀ i, ν.probability (fun x => (E i).eval x = true) ≤ δ i)
    (hcorrect : ∀ i x, (E i).eval x ≠ true → P i x = (c i).indicator x) :
    ∃ sample : GateSamplingChoices k k s,
      ν.probability (fun x => (AC0Circuit.combineGateException sample c E).eval x = true) ≤
        (7 / 8 : ℝ) ^ s + ∑ i, δ i ∧
      ∀ x, (AC0Circuit.combineGateException sample c E).eval x ≠ true →
        sampledAndPolynomial sample (fun i => P i x) = (AC0Circuit.andGate c).indicator x := by
  obtain ⟨sample, hs⟩ := exists_gateSamplingException_small ν s c
  refine ⟨sample, ?_, ?_⟩
  · let events : Option (Fin k) → BooleanCube n → Prop
      | none => fun x => (AC0Circuit.gateSamplingException sample c).eval x = true
      | some i => fun x => (E i).eval x = true
    have hcover : ∀ x,
        (AC0Circuit.combineGateException sample c E).eval x = true → ∃ i, events i x := by
      intro x hx
      rcases (AC0Circuit.combineGateException_eval sample c E x).mp hx with h | ⟨i, hi⟩
      · exact ⟨none, h⟩
      · exact ⟨some i, hi⟩
    calc
      _ ≤ ν.probability (fun x => ∃ i, events i x) := ν.probability_mono hcover
      _ ≤ ∑ i, ν.probability (events i) := ν.probability_exists_le events
      _ = ν.probability (events none) + ∑ i : Fin k, ν.probability (events (some i)) := by
        simp only [Fintype.sum_option]
      _ ≤ _ := add_le_add hs (sum_le_sum (fun i _ => hδ i))
  · intro x hx
    have hc : ∀ i, P i x = (c i).indicator x := by
      intro i
      apply hcorrect i x
      intro hi
      exact hx ((AC0Circuit.combineGateException_eval sample c E x).mpr (Or.inr ⟨i, hi⟩))
    have hp : (fun i => P i x) = fun i => (c i).indicator x := funext hc
    rw [hp]
    by_contra h
    have hlocal := sampledAndPolynomial_error_detected sample c x h
    exact hx ((AC0Circuit.combineGateException_eval sample c E x).mpr (Or.inl hlocal))

end TwoPointCorrelations

end OAI
