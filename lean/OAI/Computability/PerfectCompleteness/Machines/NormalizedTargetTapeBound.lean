import OAI.Computability.PerfectCompleteness.Foundations.SourceKeyBoundsLemmas
import OAI.Computability.PerfectCompleteness.Machines.ExactTargetOdometer
import OAI.Computability.PerfectCompleteness.Machines.TargetTapeEnvelope

namespace OAI


namespace PerfectCompleteness.NormalizedTargetTapeBound


open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)
  (input : NormalizedSourceInput.Input)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "clauses" => NormalizedSourceInput.clauses input
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "target" => NormalizedTarget.construct (t := t) rows repeats hn hbranch hrows δ input
local notation "T" => List.length (NormalizedSourceInput.bits input)
local notation "E" => List.length order

def finalData : SignedTupleBodyMachine.Data width :=
  SignedTupleSemantics.dataOfPrefix (t := t) clauses rows repeats hn hbranch hrows δ order []

def finalTapes : SignedTupleLayout.Tape width (Fin 4) → List Bool :=
  ExactTargetOdometer.nativeTapes (t := t) input
    (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩)
    (finalData (t := t) rows repeats hn hbranch hrows δ input) (fun _ => [])

theorem order_length_eq_edges : E = (target).edges.length := by
  exact (CompletedVisitOrder.completedOrder_length
    (t := t) clauses rows repeats hn hbranch hrows δ).trans
    (NormalizedTarget.edge_count (t := t) rows repeats hn hbranch hrows δ input).symm

theorem count_le : E ≤ D * (T + 1) ^ width := by
  rw [CompletedVisitOrder.completedOrder_length]
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_left
    ((SourceKeyBounds.clauseCount_le_bits input).trans (Nat.le_succ _)) _

theorem leftStream_length_le :
    (BinaryNameSearch.stream (CanonicalVertexNames.tokens
      (finalData (t := t) rows repeats hn hbranch hrows δ input).leftKeys)).length ≤
        CanonicalDictionaryNames.streamBound width T E := by
  change (BinaryNameSearch.stream (CanonicalVertexNames.tokens
    ((order).map (fun e => CanonicalGame.leftKey
      (FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats) e.1)))).length ≤ _
  have h := CanonicalVertexNames.stream_length_le
    ((order).map (fun e => CanonicalGame.leftKey
      (FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats) e.1)) T
    (by
      intro key present
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp present
      exact SourceKeyBounds.left_retained_length input rows repeats e.1)
    (by
      intro key present entry member
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp present
      exact SourceKeyBounds.left_entryID_le input rows repeats e.1 entry member)
  simpa only [List.length_map, CanonicalDictionaryNames.streamBound] using h

theorem rightStream_length_le :
    (BinaryNameSearch.stream (CanonicalVertexNames.tokens
      (finalData (t := t) rows repeats hn hbranch hrows δ input).rightKeys)).length ≤
        CanonicalDictionaryNames.streamBound width T E := by
  change (BinaryNameSearch.stream (CanonicalVertexNames.tokens
    ((order).map (fun e => CanonicalGame.rightKey
      (FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats) e.1)))).length ≤ _
  have h := CanonicalVertexNames.stream_length_le
    ((order).map (fun e => CanonicalGame.rightKey
      (FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats) e.1)) T
    (by
      intro key present
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp present
      exact SourceKeyBounds.right_retained_length input rows repeats e.1)
    (by
      intro key present entry member
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp present
      exact SourceKeyBounds.right_entryID_le input rows repeats e.1 entry member)
  simpa only [List.length_map, CanonicalDictionaryNames.streamBound] using h

theorem reversedOutput_length_le_output :
    (finalData (t := t) rows repeats hn hbranch hrows δ input).reversedOutput.length ≤
      (NormalizedTarget.outputBits (t := t) rows repeats hn hbranch hrows δ input).length := by
  have encoded := ExactTargetOnlineEncoding.target_gameBits (t := t)
    clauses rows repeats hn hbranch hrows δ
  change (Encoding.gameBits target) = _ at encoded
  change _ ≤ (Encoding.gameBits target).length
  rw [encoded]
  simp only [finalData, SignedTupleSemantics.dataOfPrefix, List.append_nil,
    List.length_reverse, List.length_append]
  omega

theorem reversedOutput_length_le :
    (finalData (t := t) rows repeats hn hbranch hrows δ input).reversedOutput.length ≤
      TargetTapeEnvelope.outputBound q E := by
  have h := (reversedOutput_length_le_output (t := t) rows repeats hn hbranch hrows δ input).trans
    (NormalizedTarget.outputBits_length_le (t := t) rows repeats hn hbranch hrows δ input)
  rw [← order_length_eq_edges (t := t) rows repeats hn hbranch hrows δ input] at h
  exact h

theorem finalTapes_length_le :
    ∀ k, (finalTapes (t := t) rows repeats hn hbranch hrows δ input k).length ≤
      TargetTapeEnvelope.bound width q T E := by
  have leftBound := leftStream_length_le (t := t) rows repeats hn hbranch hrows δ input
  have rightBound := rightStream_length_le (t := t) rows repeats hn hbranch hrows δ input
  have outputBound := reversedOutput_length_le (t := t) rows repeats hn hbranch hrows δ input
  have countBound := SourceKeyBounds.clauseCount_le_bits input
  have sourceLe : T ≤ TargetTapeEnvelope.bound width q T E := by
    unfold TargetTapeEnvelope.bound
    omega
  have currentLe : 1 ≤ TargetTapeEnvelope.bound width q T E := by
    unfold TargetTapeEnvelope.bound
    omega
  have remainingLe : NormalizedSourceInput.clauseCount input - 1 + 1 ≤
      TargetTapeEnvelope.bound width q T E := by
    unfold TargetTapeEnvelope.bound
    omega
  have leftLe := leftBound.trans (show CanonicalDictionaryNames.streamBound width T E ≤
      TargetTapeEnvelope.bound width q T E by unfold TargetTapeEnvelope.bound; omega)
  have rightLe := rightBound.trans (show CanonicalDictionaryNames.streamBound width T E ≤
      TargetTapeEnvelope.bound width q T E by unfold TargetTapeEnvelope.bound; omega)
  have outputLe := outputBound.trans (show TargetTapeEnvelope.outputBound q E ≤
      TargetTapeEnvelope.bound width q T E by unfold TargetTapeEnvelope.bound; omega)
  have encodedCountLe : E + 1 ≤ TargetTapeEnvelope.bound width q T E := by
    unfold TargetTapeEnvelope.bound
    omega
  intro k
  cases k with
  | source source =>
      cases source with
      | table => simpa [finalTapes, ExactTargetOdometer.nativeTapes,
          SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes] using sourceLe
      | digit i => simp [finalTapes, ExactTargetOdometer.nativeTapes,
          SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes]
      | work j => simp [finalTapes, ExactTargetOdometer.nativeTapes,
          SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes]
      | variableName i j => simp [finalTapes, ExactTargetOdometer.nativeTapes,
          SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes]
  | current i => simpa [finalTapes, ExactTargetOdometer.nativeTapes,
      SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes, encodeWord_length] using currentLe
  | remaining i => simpa [finalTapes, ExactTargetOdometer.nativeTapes,
      SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes, encodeWord_length] using remainingLe
  | encodedVariable i j => simp [finalTapes, ExactTargetOdometer.nativeTapes,
      SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes]
  | adapterScratch => simp [finalTapes, ExactTargetOdometer.nativeTapes,
      SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes]
  | edgeCount => simpa [finalTapes, ExactTargetOdometer.nativeTapes,
      SignedTupleBodyMachine.tapes, finalData, SignedTupleSemantics.dataOfPrefix,
      encodeWord_length] using encodedCountLe
  | extra x => simp [finalTapes, ExactTargetOdometer.nativeTapes,
      SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes]
  | edgeWork j =>
      by_cases one : j = 1
      · subst j
        simpa [finalTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
          using leftLe
      · by_cases eight : j = 8
        · subst j
          simpa [finalTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
            using rightLe
        · by_cases seven : j = 7
          · subst j
            simpa [finalTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
              using outputLe
          · simp [finalTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes,
              ExactTargetOdometer.baseTapes, one, eight, seven]

theorem finalTapes_length_le_polynomial :
    ∀ k, (finalTapes (t := t) rows repeats hn hbranch hrows δ input k).length ≤
      TargetTapeEnvelope.coeff width q D * (T + 1) ^ (2 * width + 2) := by
  intro k
  exact (finalTapes_length_le (t := t) rows repeats hn hbranch hrows δ input k).trans
    (TargetTapeEnvelope.bound_le width q D T E (count_le (t := t) rows repeats hn hbranch hrows δ input))

end
end PerfectCompleteness.NormalizedTargetTapeBound

end OAI
