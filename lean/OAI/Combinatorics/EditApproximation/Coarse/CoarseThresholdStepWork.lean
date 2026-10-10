import OAI.Combinatorics.EditApproximation.Coarse.CoarseThresholdStep

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseChildThresholdWithWork_cost (B q A : ℕ) (allowance : BinaryFraction)
    (draw : Fin B) (ha : allowance.width ≤ A)
    (hB : Nat.size B + 2 ≤ A) (hq : Nat.size q + 2 ≤ A) :
    (coarseChildThresholdWithWork B q allowance draw).2 ≤
      30000000 * (A + 1) ^ 2 := by
  have hdraw : Nat.size (draw.val + 1) + 2 ≤ A :=
    (Nat.add_le_add_right (Nat.size_le_size (show draw.val + 1 ≤ B by omega)) 2).trans hB
  have hn := (nat_width_le (draw.val + 1)).trans hdraw
  have hb := (nat_width_le B).trans hB
  have hq' := (nat_width_le q).trans hq
  have hnc := canonicalMulWithWork_cost allowance (nat (draw.val + 1)) A ha hn
  have hdc := canonicalMulWithWork_cost (nat B) (nat q) A hb hq'
  have hnw := canonicalMulWithWork_width allowance (nat (draw.val + 1)) A ha hn
  have hdw := canonicalMulWithWork_width (nat B) (nat q) A hb hq'
  have hc := coarseDivideWithWork_cost
    (canonicalMulWithWork allowance (nat (draw.val + 1))).1
    (canonicalMulWithWork (nat B) (nat q)).1 (4 * A + 2) hnw hdw
  change (canonicalMulWithWork allowance (nat (draw.val + 1))).2 +
    (canonicalMulWithWork (nat B) (nat q)).2 +
    (coarseDivideWithWork (canonicalMulWithWork allowance (nat (draw.val + 1))).1
      (canonicalMulWithWork (nat B) (nat q)).1).2 +
    Nat.size (draw.val + 1) + Nat.size B + Nat.size q + 4 ≤ _
  nlinarith only [hnc, hdc, hc, hdraw, hB, hq, Nat.zero_le A]

 theorem coarseChildAllowanceWithWork_cost (L A : ℕ) (threshold : BinaryFraction)
    (ha : threshold.width ≤ A) (hL : Nat.size L + 2 ≤ A) :
    (coarseChildAllowanceWithWork L threshold).2 ≤ 1000002 * (A + 1) ^ 2 := by
  have hc := coarseDivideWithWork_cost threshold (nat L) A ha ((nat_width_le L).trans hL)
  change (coarseDivideWithWork threshold (nat L)).2 + Nat.size L + 1 ≤ _
  nlinarith only [hc, hL, Nat.zero_le A]

end BinaryFraction
end EditApproximation

end OAI
