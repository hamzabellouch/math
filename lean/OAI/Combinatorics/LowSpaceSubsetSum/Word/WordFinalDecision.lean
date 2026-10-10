import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordMeasuredBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordInputDescriptor
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.FallbackCells
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordAddressBounds

namespace OAI

/-! # One input-only algorithm with counted preprocessing and fallback

Finite word tables represent fresh independent draws. Only the entries read
by the sequential generators are consumed; reused draws are in their counted
retained candidate buffers. The input descriptor is computed before the guard.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordFinalDecision

variable {n : ℕ}

abbrev Words (I : Instance n) := Fin (inputScale I^120) → WordDecisionRound.Words I

def run (T : DecisionThreshold) (I : Instance n) (words : Words I) : (Bool × ℕ) × ℕ :=
  let d := WordInputDescriptor.run T.value I
  let out := if h : d.guard = true then
      WordMeasuredDecision.repeated I
        (T.large.trans (of_decide_eq_true ((WordInputDescriptor.run_guard T.value I).symm.trans h)).1)
        (mainGuard_log (by unfold inputScale; omega)
          ((WordInputDescriptor.run_guard T.value I).symm.trans h)) words
    else FallbackCells.decision I
  ((out.1.1,d.work+out.1.2+3),max d.cells (out.2+8))

theorem sound (T : DecisionThreshold) (I : Instance n) (words : Words I)
    (hy : (run T I words).1.1 = true) : Solvable I := by
  dsimp only [run] at hy
  split at hy
  · exact WordMeasuredDecision.sound I _ _ words hy
  · exact (ExactFallback.decision_correct I).mp ((FallbackCells.decision_value I).symm.trans hy)

theorem probability (T : DecisionThreshold) (I : Instance n) (hs : Solvable I) :
    (2/3 : ℝ) ≤ (FiniteLaw.uniform : FiniteLaw (Words I)).probability
      (fun words => (run T I words).1.1 = true) := by
  by_cases hg : (WordInputDescriptor.run T.value I).guard = true
  · have hm := (WordInputDescriptor.run_guard T.value I).symm.trans hg
    have hn := T.large.trans (of_decide_eq_true hm).1
    have hscale := mainGuard_log (by unfold inputScale; omega : 0 < inputScale I) hm
    have he : (fun words : Words I => (run T I words).1.1 = true) =
        (fun words => (WordMeasuredDecision.repeated I hn hscale words).1.1 = true) := by
      funext words
      simp only [run,hg,↓reduceDIte]
    rw [he]
    exact (WordMeasuredDecision.probability I hn hscale
      (T.halfGap n (of_decide_eq_true hm).1) hs).le
  · have he : (fun words : Words I => (run T I words).1.1 = true) = (fun _ => True) := by
      funext words
      simp [run,hg,FallbackCells.decision_value,(ExactFallback.decision_correct I).mpr hs]
    rw [he,FiniteLaw.probability_true]
    norm_num

theorem rejects (T : DecisionThreshold) (I : Instance n) (hs : ¬Solvable I)
    (words : Words I) : (run T I words).1.1 = false := by
  apply Bool.eq_false_iff.mpr
  exact fun h => hs (sound T I words h)

private theorem overhead (u C H k l : ℕ) (hu : 10000 ≤ u) (hC : 1 ≤ C) (hH : 1 ≤ H)
    (hk : 2 ≤ k) (hl : 2 ≤ l) :
    100*u+3 ≤ u^k*H ∧ 100*u+8 ≤ u^l*C := by
  have hsmall : 100*u+8 ≤ u^2 := by nlinarith
  have ht : u^2 ≤ u^k := Nat.pow_le_pow_right (by omega) hk
  have hc : u^2 ≤ u^l := Nat.pow_le_pow_right (by omega) hl
  exact ⟨(show 100*u+3 ≤ u^2 by omega).trans (ht.trans (Nat.le_mul_of_pos_right _ hH)),
    hsmall.trans (hc.trans (Nat.le_mul_of_pos_right _ hC))⟩

theorem main_bounds (T : DecisionThreshold) (I : Instance n)
    (hm : mainGuard T.value n (inputScale I) = true) (words : Words I) :
    (run T I words).1.2 ≤ 2*(inputScale I^624*2^((n+1)/2)) ∧
    (run T I words).2 ≤ 2*writableWordLimit I := by
  have hg := (WordInputDescriptor.run_guard T.value I).trans hm
  have hn := T.large.trans (of_decide_eq_true hm).1
  have hscale := mainGuard_log (by unfold inputScale; omega : 0 < inputScale I) hm
  have hw := WordMeasuredBounds.repeated_work I hn hscale words
  have hc := WordMeasuredBounds.repeated_cells I hn hscale words
  have hdw := WordInputDescriptor.run_work T.value I
  have hdc := WordInputDescriptor.run_cells T.value I
  have hO := overhead (inputScale I) (compressionDictionaryCapacity n) (2^((n+1)/2)) 624 15
    (by unfold inputScale; omega) Nat.one_le_two_pow Nat.one_le_two_pow (by decide) (by decide)
  unfold run
  simp only [hg,↓reduceDIte]
  constructor
  · omega
  · unfold writableWordLimit at hc ⊢
    apply max_le <;> omega

theorem work_fits (T : DecisionThreshold) (I : Instance n)
    (hm : mainGuard T.value n (inputScale I) = true) (words : Words I) :
    (run T I words).1.2 < 2^wordWidth I := by
  have hn := T.large.trans (of_decide_eq_true hm).1
  have hl := mainGuard_log (by unfold inputScale; omega : 0 < inputScale I) hm
  have hc := WordExecutionAsymptotics.counter_limit I (by omega) hl
  have ht := Nat.mul_lt_mul_of_pos_left hc (by decide : 0 < 2)
  rw [←pow_succ'] at ht
  exact ((main_bounds T I hm words).1.trans_lt ht).trans_le
    (Nat.pow_le_pow_right (by decide) (by unfold wordWidth inputScale; omega))

theorem cells_fits (T : DecisionThreshold) (I : Instance n)
    (hm : mainGuard T.value n (inputScale I) = true) (words : Words I) :
    (run T I words).2 < 2^wordWidth I := by
  have hn := T.large.trans (of_decide_eq_true hm).1
  have hl := mainGuard_log (by unfold inputScale; omega : 0 < inputScale I) hm
  have hc := writableWordLimit_lt_two_pow I (by omega) hl
  have ht := Nat.mul_lt_mul_of_pos_left hc (by decide : 0 < 2)
  rw [←pow_succ'] at ht
  exact ((main_bounds T I hm words).2.trans_lt ht).trans_le
    (Nat.pow_le_pow_right (by decide) (by unfold wordWidth inputScale; omega))

end LowSpaceSubsetSum.WordFinalDecision

end

end OAI
