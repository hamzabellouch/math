import OAI.Combinatorics.EditApproximation.Binary.BinaryMedianSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryOptimizerSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryCountedGroup
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Literal exact/sample reductions and the sample-count constructor.
The child-index list cells and every comparison are included. -/

namespace EditApproximation.BinaryFraction



theorem equalAllocation_le_work (a b : BinaryFraction) :
    equalAllocation a b ≤ (equalWithWork a b).2 := by
  have hl := ltAllocation_le_work b a
  have hr := ltAllocation_le_work a b
  unfold equalAllocation equalWithWork leWithWork
  dsimp only
  omega



theorem groupTermsAllocation_le_work {M : ℕ}
    (h : BinaryFraction) (envelope values : Vector BinaryFraction M) (indices : List (Fin M)) :
    groupTermsAllocation h envelope indices ≤ (groupTermsWithWork h envelope values indices).2 := by
  apply arithmeticMapAllocation_le_work
  intro i _
  have hc := equalAllocation_le_work (envelope.get i) h
  dsimp only
  omega



theorem groupIndexAllocation_le_work {M : ℕ}
    (h : BinaryFraction) (envelope values : Vector BinaryFraction M) (indices : List (Fin M)) :
    groupIndexAllocation h envelope values indices ≤ (groupIndexWithWork h envelope values indices).2 := by
  have ht := groupTermsAllocation_le_work h envelope values indices
  have hs := sumListAllocation_le_work (groupTermsWithWork h envelope values indices).1
  unfold groupIndexAllocation groupIndexWithWork
  dsimp only
  omega

def groupScaleAllocation {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M) : ℕ :=
  let indices := if k = M then List.finRange M else (List.finRange k).map draw
  let subtotal := (groupIndexWithWork h envelope values indices).1
  let factor := if k = M then (one, 1) else divWithWork (nat M) (nat k)
  groupIndexAllocation h envelope values indices +
    (if k = M then 0 else divAllocation (nat M) (nat k)) +
    canonicalMulAllocation factor.1 subtotal + Nat.size M + Nat.size k

theorem groupScaleAllocation_le_work {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M) :
    groupScaleAllocation k h envelope values draw ≤ (groupScaleWithWork k h envelope values draw).2 := by
  let indices := if k = M then List.finRange M else (List.finRange k).map draw
  have hi := groupIndexAllocation_le_work h envelope values indices
  have hd := divAllocation_le_work (nat M) (nat k)
  have hm := canonicalMulAllocation_le_work
    (if k = M then (one, 1) else divWithWork (nat M) (nat k)).1
    (groupIndexWithWork h envelope values indices).1
  unfold groupScaleAllocation groupScaleWithWork
  dsimp only [indices] at hi hm
  dsimp only
  by_cases heq : k = M
  · simp only [ite_eq_left heq] at hi hm ⊢
    omega
  · simp only [ite_eq_right heq] at hi hm ⊢
    omega



theorem groupSampleCountAllocation_le_work (M Q b : ℕ) (h : BinaryFraction) :
    groupSampleCountAllocation M Q b h ≤ (groupSampleCountWithWork M Q b h).2 := by
  have h1 := canonicalMulAllocation_le_work (nat Q) (nat M)
  have h2 := canonicalMulAllocation_le_work (canonicalMulWithWork (nat Q) (nat M)).1 h
  have h3 := divAllocation_le_work (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)
  have h4 := naturalCeilingAllocation_le_work
    (divWithWork (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)).1
  have h5 := wordLEAllocation_le_work M.bits
    (naturalCeilingWithWork (divWithWork (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)).1).1
  unfold groupSampleCountAllocation groupSampleCountWithWork wordMinWithWork
  dsimp only
  omega

def equalInvocations (a b : BinaryFraction) : ℕ :=
  compareInvocations b a + compareInvocations a b + 3

theorem equalInvocations_le_work (a b : BinaryFraction) :
    equalInvocations a b ≤ (equalWithWork a b).2 := by
  have hl := compareInvocations_le_work b a
  have hr := compareInvocations_le_work a b
  unfold equalInvocations equalWithWork leWithWork
  dsimp only
  omega

def groupTermsInvocations {M : ℕ} (h : BinaryFraction) (envelope : Vector BinaryFraction M)
    (indices : List (Fin M)) : ℕ :=
  arithmeticMapInvocations (fun i => equalInvocations (envelope.get i) h + 1) indices

theorem groupTermsInvocations_le_work_add_one {M : ℕ}
    (h : BinaryFraction) (envelope values : Vector BinaryFraction M) (indices : List (Fin M)) :
    groupTermsInvocations h envelope indices ≤ (groupTermsWithWork h envelope values indices).2 + 1 := by
  apply arithmeticMapInvocations_le_work
  intro i _
  have hc := equalInvocations_le_work (envelope.get i) h
  dsimp only
  omega

def groupIndexInvocations {M : ℕ} (h : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (indices : List (Fin M)) : ℕ :=
  groupTermsInvocations h envelope indices +
    sumListInvocations (groupTermsWithWork h envelope values indices).1 + 1

theorem groupIndexInvocations_le_work_add_one {M : ℕ}
    (h : BinaryFraction) (envelope values : Vector BinaryFraction M) (indices : List (Fin M)) :
    groupIndexInvocations h envelope values indices ≤ (groupIndexWithWork h envelope values indices).2 + 1 := by
  have ht := groupTermsInvocations_le_work_add_one h envelope values indices
  have hs := sumListInvocations_le_work (groupTermsWithWork h envelope values indices).1
  unfold groupIndexInvocations groupIndexWithWork
  dsimp only
  omega

def groupScaleInvocations {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M) : ℕ :=
  let indices := if k = M then List.finRange M else (List.finRange k).map draw
  let subtotal := (groupIndexWithWork h envelope values indices).1
  let factor := if k = M then (one, 1) else divWithWork (nat M) (nat k)
  groupIndexInvocations h envelope values indices +
    (if k = M then 1 else divInvocations (nat M) (nat k)) +
    canonicalMulInvocations factor.1 subtotal + 1

theorem groupScaleInvocations_le_work {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M) :
    groupScaleInvocations k h envelope values draw ≤ (groupScaleWithWork k h envelope values draw).2 := by
  let indices := if k = M then List.finRange M else (List.finRange k).map draw
  have hi := groupIndexInvocations_le_work_add_one h envelope values indices
  have hd := divInvocations_le_work (nat M) (nat k)
  have hm := canonicalMulInvocations_le_work
    (if k = M then (one, 1) else divWithWork (nat M) (nat k)).1
    (groupIndexWithWork h envelope values indices).1
  unfold groupScaleInvocations groupScaleWithWork
  dsimp only [indices] at hi hm
  dsimp only
  by_cases heq : k = M
  · simp only [ite_eq_left heq] at hi hm ⊢
    omega
  · simp only [ite_eq_right heq] at hi hm ⊢
    omega

def groupSampleCountInvocations (M Q b : ℕ) (h : BinaryFraction) : ℕ :=
  let qm := (canonicalMulWithWork (nat Q) (nat M)).1
  let numerator := (canonicalMulWithWork qm h).1
  let ratio := (divWithWork numerator (nat b)).1
  canonicalMulInvocations (nat Q) (nat M) + canonicalMulInvocations qm h +
    divInvocations numerator (nat b) + naturalCeilingInvocations ratio +
    wordLEInvocations M.bits (naturalCeilingWithWork ratio).1 +
    2

theorem groupSampleCountInvocations_le_work (M Q b : ℕ) (h : BinaryFraction) :
    groupSampleCountInvocations M Q b h ≤ (groupSampleCountWithWork M Q b h).2 := by
  have h1 := canonicalMulInvocations_le_work (nat Q) (nat M)
  have h2 := canonicalMulInvocations_le_work (canonicalMulWithWork (nat Q) (nat M)).1 h
  have h3 := divInvocations_le_work (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)
  have h4 := naturalCeilingInvocations_le_work
    (divWithWork (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)).1
  have h5 := wordLEInvocations_le_work M.bits
    (naturalCeilingWithWork (divWithWork (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)).1).1
  unfold groupSampleCountInvocations groupSampleCountWithWork wordMinWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
