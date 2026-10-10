import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundedKernel

namespace OAI

/-! Boolean work for the actual canonical rounding and wide-membership
tests. Interval endpoints retain their original target bound after rounding. -/

namespace EditApproximation

theorem actionEqualWithWork_cost {n M : ℕ} (a b : Fin M → TargetInterval n) (B : ℕ)
    (hn : Nat.size n ≤ B) :
    (actionEqualWithWork a b).2 ≤ M * (16 * B + 8) := by
  have hpoint (i : Fin M) :
      (naturalEqualWithWork (a i).lo (b i).lo).2 +
        (naturalEqualWithWork (a i).hi (b i).hi).2 + 1 ≤ 16 * B + 5 := by
    have hlow := naturalEqualWithWork_cost (a i).lo (b i).lo B
      ((Nat.size_le_size ((a i).ordered.trans (a i).valid)).trans hn)
      ((Nat.size_le_size ((b i).ordered.trans (b i).valid)).trans hn)
    have hhigh := naturalEqualWithWork_cost (a i).hi (b i).hi B
      ((Nat.size_le_size (a i).valid).trans hn) ((Nat.size_le_size (b i).valid).trans hn)
    omega
  have h := allWithWork_cost (fun i =>
    let left := naturalEqualWithWork (a i).lo (b i).lo
    let right := naturalEqualWithWork (a i).hi (b i).hi
    (left.1 && right.1, left.2 + right.2 + 1)) (List.finRange M) (16 * B + 5)
    (fun i _ => hpoint i)
  simpa only [actionEqualWithWork, List.length_finRange] using h

theorem actionMemberWithWork_cost {n M : ℕ} (a : Fin M → TargetInterval n)
    (actions : List (Fin M → TargetInterval n)) (B : ℕ) (hn : Nat.size n ≤ B) :
    (actionMemberWithWork a actions).2 ≤ 1 + actions.length * (M * (16 * B + 8) + 1) := by
  induction actions with
  | nil => simp only [actionMemberWithWork, List.length_nil, Nat.zero_mul, Nat.add_zero, le_refl]
  | cons head rest ih =>
    have h := actionEqualWithWork_cost a head B hn
    change (actionEqualWithWork a head).2 + (actionMemberWithWork a rest).2 + 1 ≤ _
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem roundStateWithWork_cost {n : ℕ} (spacing : ℕ) (hspacing : 0 < spacing)
    (q : TargetInterval n) (B : ℕ) (hs : Nat.size spacing ≤ B) (hn : Nat.size n ≤ B) :
    (roundStateWithWork spacing hspacing q).2 ≤ 500 * (B + 1) ^ 2 + 1 := by
  have h := binaryIntervalRoundWithWork_cost spacing q.lo q.hi B hs
    ((Nat.size_le_size (q.ordered.trans q.valid)).trans hn)
    ((Nat.size_le_size q.valid).trans hn)
  change (binaryIntervalRoundWithWork spacing q.lo q.hi).2 + 1 ≤ _
  omega

namespace BinaryFraction

def roundedSpacingWordBudget (B : ℕ) : ℕ := 4 * B + 4

def roundedSpacingBitBudget (B : ℕ) : ℕ :=
  2000 * (B + 1) ^ 2 + 1500 * (4 * B + 3) ^ 2 + 3

theorem roundedSpacingWithWork_bounds (theta envelope : BinaryFraction) (B : ℕ)
    (ht : theta.width ≤ B) (he : envelope.width ≤ B) :
    (roundedSpacingWithWork theta envelope).1.length ≤ roundedSpacingWordBudget B ∧
      (roundedSpacingWithWork theta envelope).2 ≤ roundedSpacingBitBudget B := by
  have hp := canonicalMulWithWork_width theta envelope B ht he
  have hpc := canonicalMulWithWork_cost theta envelope B ht he
  have hm := (maxWithWork_width one (canonicalMulWithWork theta envelope).1).trans
    (show max one.width (canonicalMulWithWork theta envelope).1.width ≤ 4 * B + 2 by
      change max 1 _ ≤ _
      omega)
  have hmc := maxWithWork_cost one (canonicalMulWithWork theta envelope).1 (4 * B + 2)
    (by change 1 ≤ _; omega) hp
  have hc := naturalCeilingWithWork_length (maxWithWork one (canonicalMulWithWork theta envelope).1).1
  have hcc := naturalCeilingWithWork_cost (maxWithWork one (canonicalMulWithWork theta envelope).1).1
  have hsquare := Nat.pow_le_pow_left (show
    (maxWithWork one (canonicalMulWithWork theta envelope).1).1.width + 1 ≤ 4 * B + 3 by omega) 2
  constructor
  · change (naturalCeilingWithWork (maxWithWork one (canonicalMulWithWork theta envelope).1).1).1.length ≤ _
    unfold roundedSpacingWordBudget
    omega
  · change (canonicalMulWithWork theta envelope).2 +
      (maxWithWork one (canonicalMulWithWork theta envelope).1).2 +
      (naturalCeilingWithWork (maxWithWork one (canonicalMulWithWork theta envelope).1).1).2 + 2 ≤ _
    unfold roundedSpacingBitBudget
    nlinarith only [hpc, hmc, hcc, hsquare]

def roundedBandInputBudget (thetaExponent b M B : ℕ) : ℕ :=
  thetaExponent + 2 + 3 * bandEnvelopeWordBudget b M B + B

def roundedBandBitBudget (thetaExponent b M size B : ℕ) : ℕ :=
  let W := roundedBandInputBudget thetaExponent b M B
  M * (bandEnvelopeBitBudget b M size B + roundedSpacingBitBudget W +
    500 * (roundedSpacingWordBudget W + B + 1) ^ 2 + thetaExponent + 11)

theorem roundedBandWithWork_cost {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (initial : Fin M → TargetInterval ny → BinaryFraction) (B : ℕ)
    (hny : Nat.size ny ≤ B)
    (hi : ∀ action ∈ band, ∀ i, (initial i (action i)).width ≤ B) :
    (roundedBandWithWork thetaExponent b band hne initial).2 ≤
      roundedBandBitBudget thetaExponent b M band.length B := by
  let W := roundedBandInputBudget thetaExponent b M B
  have hW : B ≤ W := by dsimp only [W, roundedBandInputBudget]; omega
  have ht : (inversePowerTwo thetaExponent).width ≤ W := by
    rw [inversePowerTwo_width]
    dsimp only [W, roundedBandInputBudget]
    omega
  have hcell (i : Fin M) :
      (let envelope := bandEnvelopeWithWork b band initial i
       let spacing := roundedSpacingWithWork (inversePowerTwo thetaExponent) envelope.1
       let rounded := roundStateWithWork (bitWordValue spacing.1)
         (roundedSpacingWithWork_pos _ _) (band.head hne i)
       (rounded.1, envelope.2 + spacing.2 + rounded.2 + thetaExponent + 3)).2 ≤
      bandEnvelopeBitBudget b M band.length B + roundedSpacingBitBudget W +
        500 * (roundedSpacingWordBudget W + B + 1) ^ 2 + thetaExponent + 5 := by
    let envelope := bandEnvelopeWithWork b band initial i
    let spacing := roundedSpacingWithWork (inversePowerTwo thetaExponent) envelope.1
    have hew := bandEnvelopeWithWork_width b band initial i B (fun a ha => hi a ha i)
    have hec := bandEnvelopeWithWork_cost b band initial i B (fun a ha => hi a ha i)
    have heW : envelope.1.width ≤ W := hew.trans (by
      dsimp only [W, roundedBandInputBudget]; omega)
    have hs := roundedSpacingWithWork_bounds (inversePowerTwo thetaExponent) envelope.1 W ht heW
    have hss : Nat.size (bitWordValue spacing.1) ≤ roundedSpacingWordBudget W :=
      (Nat.size_le.mpr (bitWordValue_lt_pow_length spacing.1)).trans hs.1
    have hr := roundStateWithWork_cost (bitWordValue spacing.1)
      (roundedSpacingWithWork_pos _ _) (band.head hne i) (roundedSpacingWordBudget W + B)
      (by omega) (hny.trans (by omega))
    change envelope.2 + spacing.2 + (roundStateWithWork (bitWordValue spacing.1)
      (roundedSpacingWithWork_pos (inversePowerTwo thetaExponent) envelope.1)
      (band.head hne i)).2 + thetaExponent + 3 ≤ _
    change envelope.2 ≤ _ at hec
    have hsc : spacing.2 ≤ roundedSpacingBitBudget W := hs.2
    omega
  have hmap := vectorMapWithWork_cost_le M _ _ hcell
  change (vectorMapWithWork M _).2 ≤ _
  unfold roundedBandBitBudget
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hmap

end BinaryFraction
end EditApproximation

end OAI
