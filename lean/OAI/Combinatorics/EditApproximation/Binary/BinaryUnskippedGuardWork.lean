import OAI.Combinatorics.EditApproximation.Binary.BinarySelectedGroupWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandTailWork

namespace OAI

/-! All post-construction band guards, including rounded wide membership
and the child imbalance scan, have explicit Boolean arithmetic costs. -/

namespace EditApproximation
namespace BinaryFraction

def unskippedGuardInputBudget (b M B : ℕ) : ℕ :=
  let E := 3 * bandEnvelopeWordBudget b M B + 1
  B + E + bandMassTotalStorageBudget M E + stateGapWordBudget B + 10

def unskippedGuardBitBudget (e b M v w B : ℕ) : ℕ :=
  let E := 3 * bandEnvelopeWordBudget b M B + 1
  let W := unskippedGuardInputBudget b M B
  M * (bandEnvelopeBitBudget b M v B + 6) + storedSumBitBudget M E +
    2000 * (W + 1) ^ 2 + 2000 * (4 * W + 3) ^ 2 +
    (1000 * (16 * W + 11) ^ 2 + 1) + roundedBandBitBudget e b M v B +
    (1 + w * (M * (16 * B + 8) + 1)) +
    M * (18 * B + 1 + stateGapBitBudget B + 2000 * (W + 1) ^ 2 +
      (1000 * (4 * W + 3) ^ 2 + 1) + 6) + 5

theorem unskippedGuardWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (center : TargetInterval ny) (b e : ℕ) (F : BinaryFraction)
    (band wide : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (initial : Fin M → TargetInterval ny → BinaryFraction) (B : ℕ)
    (hF : F.width ≤ B) (hb : Nat.size b + 2 ≤ B)
    (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hi : ∀ action ∈ band, ∀ i, (initial i (action i)).width ≤ B) :
    (unskippedGuardWithWork parent center b e F band wide hne initial).2 ≤
      unskippedGuardBitBudget e b M band.length wide.length B := by
  let E := 3 * bandEnvelopeWordBudget b M B + 1
  let W := unskippedGuardInputBudget b M B
  let envelope := envelopeVectorWithWork b band initial
  let total := bandMassTotalWithWork envelope.1
  let fb := canonicalMulWithWork F (nat b)
  let limit := canonicalMulWithWork (nat 64) fb.1
  let rounded := roundedBandWithWork e b band hne initial
  have hBE : B ≤ W := by dsimp only [W, unskippedGuardInputBudget]; omega
  have hEW : E ≤ W := by dsimp only [E, W, unskippedGuardInputBudget]; omega
  have hW : 10 ≤ W := by dsimp only [W, unskippedGuardInputBudget]; omega
  have he (i : Fin M) : (envelope.1.get i).width ≤ E := by
    simp only [envelope, envelopeVectorWithWork, vectorMapWithWork_value]
    exact bandEnvelopeWithWork_width b band initial i B (fun a ha => hi a ha i)
  have hec := vectorMapWithWork_cost_le M (bandEnvelopeWithWork b band initial)
    (bandEnvelopeBitBudget b M band.length B)
    (fun i => bandEnvelopeWithWork_cost b band initial i B (fun a ha => hi a ha i))
  change envelope.2 ≤ _ at hec
  have htc := bandMassTotalWithWork_cost envelope.1 E he
  change total.2 ≤ _ at htc
  have htw : total.1.width ≤ bandMassTotalStorageBudget M E := by
    exact (dotListWithWork_width_le_storageBits envelope.1 (Vector.replicate M one)
      (List.finRange M)).trans (bandMassTotalWithWork_storage envelope.1 E he)
  have hstorage : bandMassTotalStorageBudget M E ≤ W := by
    dsimp only [E, W, unskippedGuardInputBudget]
    omega
  have h64 : (nat 64).width ≤ W := (nat_width_le 64).trans (by
    have h : Nat.size 64 = 7 := by decide
    omega)
  have h2 : (nat 2).width ≤ W := (nat_width_le 2).trans (by
    have h : Nat.size 2 = 2 := by decide
    omega)
  have hfbw := canonicalMulWithWork_width F (nat b) W (hF.trans hBE)
    ((nat_width_le b).trans (hb.trans hBE))
  have hfbc := canonicalMulWithWork_cost F (nat b) W (hF.trans hBE)
    ((nat_width_le b).trans (hb.trans hBE))
  change fb.1.width ≤ _ at hfbw
  change fb.2 ≤ _ at hfbc
  have hlimw := canonicalMulWithWork_width (nat 64) fb.1 (4 * W + 2) (by omega) hfbw
  have hlimc := canonicalMulWithWork_cost (nat 64) fb.1 (4 * W + 2) (by omega) hfbw
  change limit.1.width ≤ _ at hlimw
  change limit.2 ≤ _ at hlimc
  have hsum := leWithWork_cost total.1 limit.1 (16 * W + 10)
    (htw.trans (hstorage.trans (by omega))) (by omega)
  have hround := roundedBandWithWork_cost e b band hne initial B (by omega) hi
  change rounded.2 ≤ _ at hround
  have hwide := actionMemberWithWork_cost rounded.1.get wide B (by omega)
  have hgap (i : Fin M) :
      (let sourceLength := binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo
       let gap := stateGapWithWork (bitWordValue sourceLength.1) (rounded.1.get i)
       let bound := canonicalMulWithWork (nat 2) (envelope.1.get i)
       let test := leWithWork gap.1.absolute bound.1
       (test.1, sourceLength.2 + gap.2 + bound.2 + test.2 + 3)).2 ≤
        18 * B + 1 + stateGapBitBudget B + 2000 * (W + 1) ^ 2 +
          (1000 * (4 * W + 3) ^ 2 + 1) + 3 := by
    let sourceLength := binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo
    let gap := stateGapWithWork (bitWordValue sourceLength.1) (rounded.1.get i)
    let bound := canonicalMulWithWork (nat 2) (envelope.1.get i)
    have hlo : Nat.size (sourceChild parent i).lo + 2 ≤ B :=
      (Nat.add_le_add_right (Nat.size_le_size
        ((sourceChild parent i).ordered.trans (sourceChild parent i).valid)) 2).trans hnx
    have hhi : Nat.size (sourceChild parent i).hi + 2 ≤ B :=
      (Nat.add_le_add_right (Nat.size_le_size (sourceChild parent i).valid) 2).trans hnx
    have hs := binaryNaturalSubtractWithWork_cost (sourceChild parent i).hi (sourceChild parent i).lo
    have hlen : Nat.size (bitWordValue sourceLength.1) + 2 ≤ B := by
      rw [binaryNaturalSubtractWithWork_value _ _ (sourceChild parent i).ordered]
      exact (Nat.add_le_add_right (Nat.size_le_size (Nat.sub_le _ _)) 2).trans hhi
    have hg := stateGapWithWork_bounds (bitWordValue sourceLength.1) (rounded.1.get i) B hlen
      ((Nat.add_le_add_right (Nat.size_le_size ((rounded.1.get i).ordered.trans (rounded.1.get i).valid)) 2).trans hny)
      ((Nat.add_le_add_right (Nat.size_le_size (rounded.1.get i).valid) 2).trans hny)
    have hbndw := canonicalMulWithWork_width (nat 2) (envelope.1.get i) W h2 ((he i).trans hEW)
    have hbndc := canonicalMulWithWork_cost (nat 2) (envelope.1.get i) W h2 ((he i).trans hEW)
    have hgw : gap.1.width ≤ stateGapWordBudget B := hg.1
    have hgapW : stateGapWordBudget B ≤ W := by
      dsimp only [W, unskippedGuardInputBudget]
      omega
    have ht := leWithWork_cost gap.1.absolute bound.1 (4 * W + 2)
      (by change gap.1.width ≤ _; exact hgw.trans (hgapW.trans (by omega))) hbndw
    change sourceLength.2 ≤ _ at hs
    change bound.2 ≤ _ at hbndc
    change sourceLength.2 + gap.2 + bound.2 + (leWithWork gap.1.absolute bound.1).2 + 3 ≤ _
    have hgc : gap.2 ≤ stateGapBitBudget B := hg.2
    simp only [Nat.add_assoc, Nat.reduceAdd] at ht
    omega
  have hall := allWithWork_cost (fun i =>
    let sourceLength := binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo
    let gap := stateGapWithWork (bitWordValue sourceLength.1) (rounded.1.get i)
    let bound := canonicalMulWithWork (nat 2) (envelope.1.get i)
    let test := leWithWork gap.1.absolute bound.1
    (test.1, sourceLength.2 + gap.2 + bound.2 + test.2 + 3)) (List.finRange M)
    (18 * B + 1 + stateGapBitBudget B + 2000 * (W + 1) ^ 2 +
      (1000 * (4 * W + 3) ^ 2 + 1) + 3) (fun i _ => hgap i)
  simp only [List.length_finRange, Nat.add_assoc, Nat.reduceAdd] at hall hsum hlimc
  dsimp only [envelope, rounded] at hall
  change envelope.2 + total.2 + fb.2 + limit.2 + (leWithWork total.1 limit.1).2 + rounded.2 +
    (actionMemberWithWork rounded.1.get wide).2 + _ + 5 ≤ _
  dsimp only [unskippedGuardBitBudget]
  change _ ≤ M * (bandEnvelopeBitBudget b M band.length B + 6) + storedSumBitBudget M E +
    2000 * (W + 1) ^ 2 + 2000 * (4 * W + 3) ^ 2 +
    (1000 * (16 * W + 11) ^ 2 + 1) + roundedBandBitBudget e b M band.length B +
    (1 + wide.length * (M * (16 * B + 8) + 1)) +
    M * (18 * B + 1 + stateGapBitBudget B + 2000 * (W + 1) ^ 2 +
      (1000 * (4 * W + 3) ^ 2 + 1) + 6) + 5
  simp only [Nat.add_assoc, Nat.reduceAdd]
  omega

end BinaryFraction
end EditApproximation

end OAI
