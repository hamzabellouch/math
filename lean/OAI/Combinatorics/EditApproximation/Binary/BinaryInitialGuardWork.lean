import OAI.Combinatorics.EditApproximation.Binary.BinaryScaleGrid
import OAI.Combinatorics.EditApproximation.Binary.BinaryAffineGuard

namespace OAI

/-! The two initial-grid predicates are evaluated by explicit stored
multiplication, division and comparison. -/

namespace EditApproximation
namespace BinaryFraction

def initialScaleGuardBitBudget (B : ℕ) : ℕ :=
  4000 * (B + 1) ^ 2 + 4000 * (4 * B + 3) ^ 2 + 2100 * (16 * B + 12) ^ 2 +
    2 * (1000 * (64 * B + 45) ^ 2 + 1) + 2 * B + 7

def initialCenterGuardBitBudget (B : ℕ) : ℕ :=
  2100 * (B + 2) ^ 2 + 2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 11) ^ 2 + 1) + 2 * B + 5

theorem initialScaleGuardWithWork_cost (U b B : ℕ) (A : BinaryFraction)
    (hB : 8 ≤ B) (hU : Nat.size U + 2 ≤ B) (hb : Nat.size b + 2 ≤ B) (hA : A.width ≤ B) :
    (initialScaleGuardWithWork U b A).2 ≤ initialScaleGuardBitBudget B := by
  have h16 : (nat 16).width ≤ B := (nat_width_le 16).trans (by change 7 ≤ B; omega)
  have h4 : (nat 4).width ≤ B := (nat_width_le 4).trans (by change 5 ≤ B; omega)
  have hUn := (nat_width_le U).trans hU
  have hbn := (nat_width_le b).trans hb
  have hsw := canonicalMulWithWork_width A A B hA hA
  have hsc := canonicalMulWithWork_cost A A B hA hA
  have hdw := canonicalMulWithWork_width (nat 16) (canonicalMulWithWork A A).1 (4 * B + 2) (by omega) hsw
  have hdc := canonicalMulWithWork_cost (nat 16) (canonicalMulWithWork A A).1 (4 * B + 2) (by omega) hsw
  have hlw := divWithWork_width_uniform (nat U)
    (canonicalMulWithWork (nat 16) (canonicalMulWithWork A A).1).1 (16 * B + 10) (by omega) (by omega)
  have hlc := divWithWork_cost (nat U)
    (canonicalMulWithWork (nat 16) (canonicalMulWithWork A A).1).1 (16 * B + 10) (by omega) (by omega)
  have hfw := canonicalMulWithWork_width (nat 4) A B h4 hA
  have hfc := canonicalMulWithWork_cost (nat 4) A B h4 hA
  have huw := canonicalMulWithWork_width (canonicalMulWithWork (nat 4) A).1 (nat U)
    (4 * B + 2) hfw (by omega)
  have huc := canonicalMulWithWork_cost (canonicalMulWithWork (nat 4) A).1 (nat U)
    (4 * B + 2) hfw (by omega)
  have hlow := leWithWork_cost
    (divWithWork (nat U) (canonicalMulWithWork (nat 16) (canonicalMulWithWork A A).1).1).1
    (nat b) (64 * B + 44) (by omega) (by omega)
  have hhigh := leWithWork_cost (nat b)
    (canonicalMulWithWork (canonicalMulWithWork (nat 4) A).1 (nat U)).1
    (64 * B + 44) (by omega) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hdc hlc huc hlow hhigh
  change _ + _ + _ + _ + _ + _ + _ + Nat.size U + Nat.size b + 7 ≤ _
  unfold initialScaleGuardBitBudget
  omega

theorem initialCenterGuardWithWork_cost (b U B : ℕ) (A : BinaryFraction)
    (hB : 8 ≤ B) (hb : Nat.size b + 2 ≤ B) (hU : Nat.size U + 2 ≤ B) (hA : A.width ≤ B) :
    (initialCenterGuardWithWork b U A).2 ≤ initialCenterGuardBitBudget B := by
  have h2 : (nat 2).width ≤ B := (nat_width_le 2).trans (by change 4 ≤ B; omega)
  have h4 : (nat 4).width ≤ B := (nat_width_le 4).trans (by change 5 ≤ B; omega)
  have hUn := (nat_width_le U).trans hU
  have hbn := (nat_width_le b).trans hb
  have hlw := divWithWork_width_uniform (nat b) (nat 2) B hbn h2
  have hlc := divWithWork_cost (nat b) (nat 2) B hbn h2
  have hfw := canonicalMulWithWork_width (nat 4) A B h4 hA
  have hfc := canonicalMulWithWork_cost (nat 4) A B h4 hA
  have huw := canonicalMulWithWork_width (canonicalMulWithWork (nat 4) A).1 (nat b)
    (4 * B + 2) hfw (by omega)
  have huc := canonicalMulWithWork_cost (canonicalMulWithWork (nat 4) A).1 (nat b)
    (4 * B + 2) hfw (by omega)
  have hlow := leWithWork_cost (divWithWork (nat b) (nat 2)).1 (nat U)
    (16 * B + 10) (by omega) (by omega)
  have hhigh := leWithWork_cost (nat U)
    (canonicalMulWithWork (canonicalMulWithWork (nat 4) A).1 (nat b)).1
    (16 * B + 10) (by omega) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hlc huc hlow hhigh
  change _ + _ + _ + _ + _ + Nat.size b + Nat.size U + 5 ≤ _
  unfold initialCenterGuardBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
