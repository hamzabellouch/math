import OAI.Combinatorics.EditApproximation.Binary.BinaryCountedGroup

namespace OAI

/-! The count used by every sampled scale is at most the actual child
arity. Consequently the complete group counter is bounded from stored
input widths, without assuming estimates on its internal callbacks. -/

namespace EditApproximation
namespace BinaryFraction

private theorem sumStorage_mono {n m B : ℕ} (h : n ≤ m) :
    bandMassTotalStorageBudget n B ≤ bandMassTotalStorageBudget m B := by
  have hs := Nat.size_le_size h
  unfold bandMassTotalStorageBudget
  gcongr

private theorem storedSumWork_mono {n m B : ℕ} (h : n ≤ m) :
    storedSumBitBudget n B ≤ storedSumBitBudget m B := by
  have hs := Nat.size_le_size h
  unfold storedSumBitBudget storedSumWordBudget
  gcongr

def boundedScaleWordBudget (M B : ℕ) : ℕ :=
  4 * (4 * B + 4 + bandMassTotalStorageBudget M B) + 2

def boundedScaleBitBudget (M B : ℕ) : ℕ :=
  groupIndexBitBudget M B + (2100 * (B + 2) ^ 2 + 1) +
    2000 * (4 * B + 4 + bandMassTotalStorageBudget M B + 1) ^ 2 + 2 * B + 3

private theorem groupScale_budget_le (M k B : ℕ) (hk : k ≤ M) :
    groupScaleWordBudget M k B ≤ boundedScaleWordBudget M B ∧
      groupScaleBitBudget M k B ≤ boundedScaleBitBudget M B := by
  have ht : groupScaleTermCount M k ≤ M := by
    unfold groupScaleTermCount
    split_ifs <;> omega
  have hsum := sumStorage_mono (B := B) ht
  have hwork := storedSumWork_mono (B := B) ht
  constructor
  · unfold groupScaleWordBudget boundedScaleWordBudget
    omega
  · unfold groupScaleBitBudget boundedScaleBitBudget groupIndexBitBudget
    have hprod := Nat.mul_le_mul_right (2 * (1000 * (B + 1) ^ 2 + 1) + 6) ht
    have hsq := Nat.pow_le_pow_left (show
      4 * B + 4 + bandMassTotalStorageBudget (groupScaleTermCount M k) B + 1 ≤
        4 * B + 4 + bandMassTotalStorageBudget M B + 1 by omega) 2
    omega

def countedGroupBitBudget (M T B : ℕ) : ℕ :=
  T * (groupSampleCountBitBudget B + 6) +
    groupMemberBitBudget T B (boundedScaleBitBudget M B) (boundedScaleWordBudget M B) + 1

theorem countedGroupMemberWithWork_bounds {M T : ℕ} (Q b : ℕ) (scales : Fin T → BinaryFraction)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)
    (B : ℕ) (hB : 1 ≤ B) (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hs : ∀ t, (scales t).width ≤ B)
    (hconn : connection.width ≤ B) (he : ∀ i, (envelope.get i).width ≤ B)
    (hv : ∀ i, (values.get i).width ≤ B) :
    (countedGroupMemberWithWork Q b scales connection envelope values draw).1.width ≤
        groupMemberWordBudget T B (boundedScaleWordBudget M B) ∧
      (countedGroupMemberWithWork Q b scales connection envelope values draw).2 ≤
        countedGroupBitBudget M T B := by
  have hk (t : Fin T) : groupSampleCount M Q b (scales t).value ≤ M := by
    exact min_le_left _ _
  have hscale (t : Fin T) := groupScaleWithWork_bounds
    (groupSampleCount M Q b (scales t).value) (scales t) envelope values (draw t) B
    hB (hs t) he hv hM ((Nat.add_le_add_right (Nat.size_le_size (hk t)) 2).trans hM)
  have hc (t : Fin T) := (hscale t).2.trans (groupScale_budget_le M _ B (hk t)).2
  have hw (t : Fin T) := (hscale t).1.trans (groupScale_budget_le M _ B (hk t)).1
  constructor
  · have hmember := (groupMemberWithWork_bounds scales
      (fun t => groupSampleCount M Q b (scales t).value) connection envelope values draw B
      (boundedScaleBitBudget M B) (boundedScaleWordBudget M B) hconn hc hw).1
    unfold countedGroupMemberWithWork
    dsimp only
    rw [groupMemberWithWork_transport]
    exact hmember
  · exact countedGroupMemberWithWork_cost Q b scales connection envelope values draw B
      (boundedScaleBitBudget M B) (boundedScaleWordBudget M B) hM hQ hb hs hconn hc hw

end BinaryFraction
end EditApproximation

end OAI
