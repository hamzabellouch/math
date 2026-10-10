import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedRootCost
import OAI.Combinatorics.EditApproximation.Coarse.CoarseWeightSimulation

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem coarseRootReadExtra_bound {B d : ℕ} (k q L K : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (hK : 1 ≤ K) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d)
    (budget : CoarseReadBudget B d k (coarseEntryWidth x y) x y K) :
    coarseRootReadExtra k q L hB hq hL x y draws ≤
      (32 * K) * (2 * coarseActiveArrayWork k q (1 / L)
        (coarseEntryTree B d x y) draws k + 1) := by
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := coarseGridNatWithWork den.1 denPos 2
  let allowance := coarseGridNatWithWork den.1 denPos k
  have he := coarseIndexedExtra_bound d k q L (coarseEntryWidth x y) K x y two.1 hB hK
    (le_max_left _ _) budget d 0 draws allowance.1 0 le_rfl (by omega)
    (by simp only [coarseDescriptorLength, Nat.sub_zero, Nat.zero_add]; exact min_le_right _ _)
  simp only [Nat.zero_add, coarseReadTree_entry] at he
  have ha : allowance.1.representation.den = coarseCommonDenominator 1 q L B d :=
    (coarseGridNatWithWork_den _ _ k).trans (coarseRootDenominator_value B q L d)
  have hv : allowance.1.value = k := coarseGridNatWithWork_value _ _ k
  have hp : allowance.1.value.den ∣ (L * B * q) ^ 0 := by
    rw [hv, Rat.den_natCast]
    exact one_dvd _
  have hw := coarseBinaryWeight_le k q L d (coarseEntryTree B d x y) draws hB hq hL
    0 (by omega) allowance.1 ha hp
  rw [hv] at hw
  change coarseIndexedExtra k q L (coarseEntryWidth x y) x y two.1 d 0 draws allowance.1 0 ≤ _
  exact he.trans (Nat.mul_le_mul_left (32 * K) hw)

end BinaryFraction
end EditApproximation

end OAI
