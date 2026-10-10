import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundingSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryUnskippedReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem gapGuardAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (envelope : Vector BinaryFraction M) (rounded : Vector (TargetInterval ny) M) (i : Fin M) :
    gapGuardAllocation parent envelope rounded i ≤
      (binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo).2 +
      (stateGapWithWork (bitWordValue (binaryNaturalSubtractWithWork (sourceChild parent i).hi
        (sourceChild parent i).lo).1) (rounded.get i)).2 +
      (canonicalMulWithWork (nat 2) (envelope.get i)).2 +
      (leWithWork (stateGapWithWork (bitWordValue (binaryNaturalSubtractWithWork (sourceChild parent i).hi
        (sourceChild parent i).lo).1) (rounded.get i)).1.absolute
        (canonicalMulWithWork (nat 2) (envelope.get i)).1).2 + 3 := by
  have hs := bitSubtractAllocation_le_work (sourceChild parent i).hi.bits (sourceChild parent i).lo.bits false
  have hg := stateGapAllocation_le_work
    (bitWordValue (binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo).1)
    (rounded.get i)
  have hm := canonicalMulAllocation_le_work (nat 2) (envelope.get i)
  have hl := leAllocation_le_work
    (stateGapWithWork (bitWordValue (binaryNaturalSubtractWithWork (sourceChild parent i).hi
      (sourceChild parent i).lo).1) (rounded.get i)).1.absolute
    (canonicalMulWithWork (nat 2) (envelope.get i)).1
  unfold gapGuardAllocation
  dsimp only
  have hs' : bitSubtractAllocation (sourceChild parent i).hi.bits (sourceChild parent i).lo.bits false ≤
      (binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo).2 := hs
  omega



theorem unskippedGuardReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (center : TargetInterval ny) (b exponent : ℕ) (F : BinaryFraction)
    (band wide : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ)
    (h : ∀ i q, allocation i q ≤ (read i q).2) :
    unskippedGuardReadAllocation parent center b exponent F band wide hne read allocation ≤
      (unskippedGuardReadWithWork parent center b exponent F band wide hne read).2 := by
  let envelope := (envelopeVectorReadWithWork b band read).1
  let rounded := (roundedBandReadWithWork exponent b band hne read).1
  have he := envelopeVectorReadAllocation_le_work b band read allocation (fun i action _ => h i (action i))
  have ht := bandMassAllocation_le_work envelope
  have hf := canonicalMulAllocation_le_work F (nat b)
  have hl := canonicalMulAllocation_le_work (nat 64) (canonicalMulWithWork F (nat b)).1
  have hs := leAllocation_le_work (bandMassTotalWithWork envelope).1
    (canonicalMulWithWork (nat 64) (canonicalMulWithWork F (nat b)).1).1
  have hr := roundedBandReadAllocation_le_work exponent b band hne read allocation h
  have hw := actionMemberAllocation_le_work rounded.get wide
  have hg := allAllocation_le_work (fun i =>
    let sourceLength := binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo
    let gap := stateGapWithWork (bitWordValue sourceLength.1) (rounded.get i)
    let bound := canonicalMulWithWork (nat 2) (envelope.get i)
    let test := leWithWork gap.1.absolute bound.1
    (test.1, sourceLength.2 + gap.2 + bound.2 + test.2 + 3))
    (gapGuardAllocation parent envelope rounded) (List.finRange M)
    (fun i _ => gapGuardAllocation_le_work parent envelope rounded i)
  unfold unskippedGuardReadAllocation unskippedGuardReadWithWork
  dsimp only [envelope, rounded] at ht hs hw hg ⊢
  omega



theorem preparedUnskippedReadAllocation_le_work {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (center : TargetInterval target.length)
    (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P) (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (readAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (ha : ∀ i q, readAllocation i q ≤ (read i q).2)
    (hinit : ∀ i q, initialAllocation i q ≤ (initial i q).2) :
    preparedUnskippedReadAllocation parent center b P exponent tau F read initial readAllocation initialAllocation ≤
      (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F read initial R C hr hi center).2 := by
  have costBound (a a' w w' g g' l k k' : ℕ)
      (ha : a ≤ a') (hw : w ≤ w') (hg : g ≤ g') (hk : k ≤ k') :
      a + (w + l + g + k) ≤ a' + w' + g' + l + k' := by
    omega
  have hbnd := preparedRepresentativeReadAllocation_le_work parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) read readAllocation ha
  have hw := wideActionGridAllocation_le_work M parent center b P
  unfold preparedUnskippedReadAllocation preparedUnskippedReadWithWork
  dsimp only
  split_ifs with hband hguard
  · exact Nat.add_le_add hbnd (by decide : 0 ≤ 1)
  · have hg := unskippedGuardReadAllocation_le_work parent center b exponent F
      (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P tau (inversePowerTwo exponent) read).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hband initial initialAllocation hinit
    dsimp only
    exact costBound _ _ _ _ _ _ _ 3 3 hbnd hw hg (Nat.le_refl _)
  · have hg := unskippedGuardReadAllocation_le_work parent center b exponent F
      (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P tau (inversePowerTwo exponent) read).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hband initial initialAllocation hinit
    dsimp only
    exact costBound _ _ _ _ _ _ _ 0 2 hbnd hw hg (by decide : 0 ≤ 2)

end EditApproximation.BinaryFraction

end OAI
