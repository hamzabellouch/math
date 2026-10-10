import OAI.Combinatorics.EditApproximation.Queries.QueryDataBuffers
import OAI.Combinatorics.EditApproximation.Binary.BinaryBufferSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- Materializing the two natural-word encodings fits the comparison loop. -/
theorem bitCompareWithWork_input_cells (left right : List Bool) :
    left.length + right.length ≤ (bitCompareWithWork left right).2 := by
  induction left generalizing right with
  | nil =>
    simp only [bitCompareWithWork]
    induction right with
    | nil => decide
    | cons bit rest ih =>
      simp only [bitCompareNilLeftWithWork, List.length_nil, List.length_cons] at *
      omega
  | cons bit rest ih =>
    cases right with
    | nil =>
      have h := ih []
      simp only [bitCompareWithWork, List.length_nil, List.length_cons] at *
      omega
    | cons bit' rest' =>
      have h := ih rest'
      simp only [bitCompareWithWork, List.length_cons] at *
      omega



theorem naturalEqualAllocation_le_work (a b : ℕ) :
    naturalEqualAllocation a b ≤ (naturalEqualWithWork a b).2 :=
  Nat.add_le_add_right (bitCompareWithWork_input_cells a.bits b.bits) 1



theorem coordinateEqualAllocation_le_work {M n : ℕ} (a b : Fin M × TargetInterval n) :
    coordinateEqualAllocation a b ≤ (coordinateEqualWithWork a b).2 := by
  have hi := naturalEqualAllocation_le_work a.1.val b.1.val
  have hl := naturalEqualAllocation_le_work a.2.lo b.2.lo
  have hh := naturalEqualAllocation_le_work a.2.hi b.2.hi
  unfold coordinateEqualAllocation coordinateEqualWithWork
  dsimp only
  omega



theorem queryHistoryEqualAllocation_le_work {M n : ℕ} (a b : Fin M × ℕ × TargetInterval n) :
    queryHistoryEqualAllocation a b ≤ (queryHistoryEqualWithWork a b).2 := by
  have hc := coordinateEqualAllocation_le_work (a.1, a.2.2) (b.1, b.2.2)
  have ht := naturalEqualAllocation_le_work a.2.1 b.2.1
  unfold queryHistoryEqualAllocation queryHistoryEqualWithWork
  dsimp only
  omega



theorem queryIntervalEqualAllocation_le_work {n : ℕ} (a b : TargetInterval n) :
    queryIntervalEqualAllocation a b ≤ (queryIntervalEqualWithWork a b).2 := by
  have hl := naturalEqualAllocation_le_work a.lo b.lo
  have hh := naturalEqualAllocation_le_work a.hi b.hi
  unfold queryIntervalEqualAllocation queryIntervalEqualWithWork
  dsimp only
  omega



theorem queryOnlineKeyEqualAllocation_le_work {n : ℕ} (a b : ℕ × TargetInterval n) :
    queryOnlineKeyEqualAllocation a b ≤ (queryOnlineKeyEqualWithWork a b).2 := by
  have hs := naturalEqualAllocation_le_work a.1 b.1
  have hi := queryIntervalEqualAllocation_le_work a.2 b.2
  unfold queryOnlineKeyEqualAllocation queryOnlineKeyEqualWithWork
  dsimp only
  omega



theorem queryGroupKeyEqualAllocation_le_work {M F Q : ℕ} (a b : GroupScalarKey M F Q) :
    queryGroupKeyEqualAllocation a b ≤ (queryGroupKeyEqualWithWork a b).2 := by
  have h1 := naturalEqualAllocation_le_work a.1.1 b.1.1
  have h2 := naturalEqualAllocation_le_work a.1.2.1 b.1.2.1
  have h3 := naturalEqualAllocation_le_work a.1.2.2 b.1.2.2
  have h4 := naturalEqualAllocation_le_work a.2.1.val b.2.1.val
  have h5 := naturalEqualAllocation_le_work a.2.2.val b.2.2.val
  unfold queryGroupKeyEqualAllocation queryGroupKeyEqualWithWork
  dsimp only
  omega

def naturalEqualInvocations (a b : ℕ) : ℕ := bitCompareInvocations a.bits b.bits + 1

theorem naturalEqualInvocations_le_work (a b : ℕ) :
    naturalEqualInvocations a b ≤ (naturalEqualWithWork a b).2 :=
  Nat.add_le_add_right (bitCompareInvocations_le_work a.bits b.bits) 1

def coordinateEqualInvocations {M n : ℕ} (a b : Fin M × TargetInterval n) : ℕ :=
  naturalEqualInvocations a.1.val b.1.val + naturalEqualInvocations a.2.lo b.2.lo +
    naturalEqualInvocations a.2.hi b.2.hi + 1

theorem coordinateEqualInvocations_le_work {M n : ℕ} (a b : Fin M × TargetInterval n) :
    coordinateEqualInvocations a b ≤ (coordinateEqualWithWork a b).2 := by
  have hi := naturalEqualInvocations_le_work a.1.val b.1.val
  have hl := naturalEqualInvocations_le_work a.2.lo b.2.lo
  have hh := naturalEqualInvocations_le_work a.2.hi b.2.hi
  unfold coordinateEqualInvocations coordinateEqualWithWork
  dsimp only
  omega

def queryHistoryEqualInvocations {M n : ℕ} (a b : Fin M × ℕ × TargetInterval n) : ℕ :=
  coordinateEqualInvocations (a.1, a.2.2) (b.1, b.2.2) + naturalEqualInvocations a.2.1 b.2.1 + 1

theorem queryHistoryEqualInvocations_le_work {M n : ℕ} (a b : Fin M × ℕ × TargetInterval n) :
    queryHistoryEqualInvocations a b ≤ (queryHistoryEqualWithWork a b).2 := by
  have hc := coordinateEqualInvocations_le_work (a.1, a.2.2) (b.1, b.2.2)
  have ht := naturalEqualInvocations_le_work a.2.1 b.2.1
  unfold queryHistoryEqualInvocations queryHistoryEqualWithWork
  dsimp only
  omega

namespace BinaryFraction



theorem queryChildReadAllocation_le_work {M n : ℕ} (keys : List (Fin M × TargetInterval n))
    (values : List BinaryFraction) (i : Fin M) (q : TargetInterval n) :
    queryChildReadAllocation keys values i q ≤ (queryChildReadWithWork keys values i q).2 :=
  gatheredLookupAllocation_le_work _ _ _ _ _ (fun key _ => coordinateEqualAllocation_le_work _ key)



theorem queryHistoryReadAllocation_le_work {M n : ℕ} (keys : List (Fin M × ℕ × TargetInterval n))
    (values : List BinaryFraction) (s : ℕ) (input : Fin M × TargetInterval n) :
    queryHistoryReadAllocation keys values s input ≤ (queryHistoryReadWithWork keys values s input).2 :=
  gatheredLookupAllocation_le_work _ _ _ _ _ (fun key _ => queryHistoryEqualAllocation_le_work _ key)



theorem naturalFloorAllocation_le_work (a : BinaryFraction) :
    naturalFloorAllocation a ≤ (naturalFloorWithWork a).2 := by
  have h := bitDivModAllocation_le_work a.denominator a.numerator.bits
  unfold naturalFloorAllocation naturalFloorWithWork
  split_ifs <;> dsimp only <;> omega



theorem queryOnlineIntegerReadAllocation_le_work {n : ℕ} (keys : List (ℕ × TargetInterval n))
    (values : List BinaryFraction) (b : ℕ) (q : TargetInterval n) :
    queryOnlineIntegerReadAllocation keys values b q ≤ (queryOnlineIntegerReadWithWork keys values b q).2 := by
  have hl := gatheredLookupAllocation_le_work queryOnlineKeyEqualWithWork queryOnlineKeyEqualAllocation
    keys values (b, q) (fun key _ => queryOnlineKeyEqualAllocation_le_work _ key)
  have hf := naturalFloorAllocation_le_work (gatheredWordLookupWithWork queryOnlineKeyEqualWithWork keys values (b, q)).1
  unfold queryOnlineIntegerReadAllocation queryOnlineIntegerReadWithWork
  dsimp only
  omega



theorem queryGroupDrawReadAllocation_le_work {M F Q : ℕ} [NeZero M]
    (keys : List (GroupScalarKey M F Q)) (values : List BinaryFraction)
    (b : ℕ) (cell : ℕ × ℕ) (scale : Fin (groupDyadicScales M b F).length)
    (sample : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale))) :
    queryGroupDrawReadAllocation keys values b cell scale sample ≤
      (queryGroupDrawReadWithWork keys values b cell scale sample).2 := by
  let key : GroupScalarKey M F Q := ⟨(b, cell), scale, sample⟩
  have hl := gatheredLookupAllocation_le_work queryGroupKeyEqualWithWork queryGroupKeyEqualAllocation
    keys values key (fun key' _ => queryGroupKeyEqualAllocation_le_work key key')
  have hf := naturalFloorAllocation_le_work (gatheredWordLookupWithWork queryGroupKeyEqualWithWork keys values key).1
  have hd := bitDivModAllocation_le_work M.bits
    (bitWordValue (naturalFloorWithWork (gatheredWordLookupWithWork queryGroupKeyEqualWithWork keys values key).1).1).bits
  unfold queryGroupDrawReadAllocation queryGroupDrawReadWithWork binaryNaturalDivModWithWork
  dsimp only [key] at hl hf hd ⊢
  omega

def queryChildReadInvocations {M n : ℕ} (keys : List (Fin M × TargetInterval n))
    (values : List BinaryFraction) (i : Fin M) (q : TargetInterval n) : ℕ :=
  gatheredLookupInvocations coordinateEqualWithWork coordinateEqualInvocations keys values (i, q)

theorem queryChildReadInvocations_le_work {M n : ℕ} (keys : List (Fin M × TargetInterval n))
    (values : List BinaryFraction) (i : Fin M) (q : TargetInterval n) :
    queryChildReadInvocations keys values i q ≤ (queryChildReadWithWork keys values i q).2 :=
  gatheredLookupInvocations_le_work _ _ _ _ _ (fun key _ => coordinateEqualInvocations_le_work _ key)

def queryHistoryReadInvocations {M n : ℕ} (keys : List (Fin M × ℕ × TargetInterval n))
    (values : List BinaryFraction) (s : ℕ) (input : Fin M × TargetInterval n) : ℕ :=
  gatheredLookupInvocations queryHistoryEqualWithWork queryHistoryEqualInvocations keys values (input.1, s, input.2)

theorem queryHistoryReadInvocations_le_work {M n : ℕ} (keys : List (Fin M × ℕ × TargetInterval n))
    (values : List BinaryFraction) (s : ℕ) (input : Fin M × TargetInterval n) :
    queryHistoryReadInvocations keys values s input ≤ (queryHistoryReadWithWork keys values s input).2 :=
  gatheredLookupInvocations_le_work _ _ _ _ _ (fun key _ => queryHistoryEqualInvocations_le_work _ key)

end BinaryFraction
end EditApproximation

end OAI
