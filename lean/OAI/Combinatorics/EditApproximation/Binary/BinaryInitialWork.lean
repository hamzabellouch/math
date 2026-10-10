import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialKernel
import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeWork

namespace OAI

/-! Input-width bounds for executed ceilings and initial-cone arithmetic. -/

namespace EditApproximation
namespace BinaryFraction

def scaledSeedWordBudget (B : ℕ) : ℕ := 4 * B + 6

def scaledSeedBitBudget (B : ℕ) : ℕ :=
  2100 * (B + 2) ^ 2 + 500 * (4 * B + 5) ^ 2 +
    (1000 * (4 * B + 7) ^ 2 + 1) + B + 3

theorem scaledSeedWithWork_bounds (U : ℕ) (a gap : BinaryFraction) (B : ℕ)
    (_hB : 1 ≤ B) (hU : Nat.size U + 2 ≤ B) (ha : a.width ≤ B) (hg : gap.width ≤ B) :
    (scaledSeedWithWork U a gap).1.width ≤ scaledSeedWordBudget B ∧
      (scaledSeedWithWork U a gap).2 ≤ scaledSeedBitBudget B := by
  have hUw := (nat_width_le U).trans hU
  have hrw := divWithWork_width_uniform (nat U) a B hUw ha
  have hrc := divWithWork_cost (nat U) a B hUw ha
  have hcw := naturalCeilingWithWork_length (divWithWork (nat U) a).1
  have hcc := naturalCeilingWithWork_cost (divWithWork (nat U) a).1
  have hp := Nat.pow_le_pow_left (show (divWithWork (nat U) a).1.width + 1 ≤ 4 * B + 5 by omega) 2
  have hround : (ofNaturalWord (naturalCeilingWithWork (divWithWork (nat U) a).1).1).width ≤ 4 * B + 6 := by
    rw [ofNaturalWord_width]
    omega
  have hgw : gap.absolute.width ≤ 4 * B + 6 := (absolute_width gap).le.trans (by omega)
  have hmw := maxWithWork_width (ofNaturalWord (naturalCeilingWithWork (divWithWork (nat U) a).1).1) gap.absolute
  have hmc := maxWithWork_cost (ofNaturalWord (naturalCeilingWithWork (divWithWork (nat U) a).1).1)
    gap.absolute (4 * B + 6) hround hgw
  constructor
  · change (maxWithWork (ofNaturalWord (naturalCeilingWithWork (divWithWork (nat U) a).1).1)
      gap.absolute).1.width ≤ scaledSeedWordBudget B
    unfold scaledSeedWordBudget
    omega
  · change _ + _ + _ + Nat.size U + 3 ≤ _
    simp only [Nat.add_assoc, Nat.reduceAdd] at hmc
    unfold scaledSeedBitBudget
    omega

def initialConeInputBudget (B : ℕ) : ℕ := B + endpointDistanceWordBudget B + stateGapWordBudget B

def initialConeWordBudget (B : ℕ) : ℕ := 32 * initialConeInputBudget B + 54

def initialConeBitBudget (B : ℕ) : ℕ :=
  stateGapBitBudget B + scaledSeedBitBudget (initialConeInputBudget B) + endpointDistanceBitBudget B +
    2000 * (initialConeInputBudget B + 1) ^ 2 +
    6000 * (4 * initialConeInputBudget B + 7) ^ 2 + 4

theorem initialConeWithWork_bounds {n : ℕ} (sourceLength : ℕ) (U : TargetInterval n → ℕ)
    (a L : BinaryFraction) (query center : TargetInterval n) (B : ℕ) (hB : 1 ≤ B)
    (hs : Nat.size sourceLength + 2 ≤ B) (hU : Nat.size (U center) + 2 ≤ B)
    (ha : a.width ≤ B) (hL : L.width ≤ B)
    (hql : Nat.size query.lo + 2 ≤ B) (hqh : Nat.size query.hi + 2 ≤ B)
    (hcl : Nat.size center.lo + 2 ≤ B) (hch : Nat.size center.hi + 2 ≤ B) :
    (initialConeWithWork sourceLength U a L query center).1.width ≤ initialConeWordBudget B ∧
      (initialConeWithWork sourceLength U a L query center).2 ≤ initialConeBitBudget B := by
  let W := initialConeInputBudget B
  have hBW : B ≤ W := by dsimp only [W, initialConeInputBudget]; omega
  have hgap := stateGapWithWork_bounds sourceLength center B hs hcl hch
  have hdist := endpointDistanceWithWork_bounds query center B hql hqh hcl hch
  have hgapW : (stateGapWithWork sourceLength center).1.width ≤ W := hgap.1.trans (by
    dsimp only [W, initialConeInputBudget]; omega)
  have hdistW : (endpointDistanceWithWork query center).1.width ≤ W := hdist.1.trans (by
    dsimp only [W, initialConeInputBudget]; omega)
  have hseed := scaledSeedWithWork_bounds (U center) a (stateGapWithWork sourceLength center).1 W
    (hB.trans hBW) (hU.trans hBW) (ha.trans hBW) hgapW
  have hspw := canonicalMulWithWork_width L (endpointDistanceWithWork query center).1 W
    (hL.trans hBW) hdistW
  have hspc := canonicalMulWithWork_cost L (endpointDistanceWithWork query center).1 W
    (hL.trans hBW) hdistW
  have hseedW : (scaledSeedWithWork (U center) a (stateGapWithWork sourceLength center).1).1.width ≤ 4 * W + 6 :=
    hseed.1
  have hlastw := canonicalAddWithWork_width
    (scaledSeedWithWork (U center) a (stateGapWithWork sourceLength center).1).1
    (canonicalMulWithWork L (endpointDistanceWithWork query center).1).1 (4 * W + 6) hseedW (by omega)
  have hlastc := canonicalAddWithWork_cost
    (scaledSeedWithWork (U center) a (stateGapWithWork sourceLength center).1).1
    (canonicalMulWithWork L (endpointDistanceWithWork query center).1).1 (4 * W + 6) hseedW (by omega)
  constructor
  · change (canonicalAddWithWork (scaledSeedWithWork (U center) a (stateGapWithWork sourceLength center).1).1
      (canonicalMulWithWork L (endpointDistanceWithWork query center).1).1).1.width ≤ initialConeWordBudget B
    unfold initialConeWordBudget
    change _ ≤ 32 * W + 54
    omega
  · change _ + _ + _ + _ + _ + 4 ≤ _
    simp only [Nat.add_assoc, Nat.reduceAdd] at hlastc
    unfold initialConeBitBudget
    change _ ≤ stateGapBitBudget B + scaledSeedBitBudget W + endpointDistanceBitBudget B +
      2000 * (W + 1) ^ 2 + 6000 * (4 * W + 7) ^ 2 + 4
    omega

end BinaryFraction
end EditApproximation

end OAI
