import OAI.Combinatorics.EditApproximation.Binary.BinaryPhysicalContinuation
import OAI.Combinatorics.EditApproximation.Binary.BinaryPowerStorage
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Cache insertion compresses the actual continuation result by executed
Boolean multiplication and division. Its cost is part of the return
counter; no rational normalization operation is assigned unit cost. -/

namespace EditApproximation
namespace BinaryFraction



theorem finishCachedWithWork_value (raw : BinaryFraction × ℕ) (base : List Bool)
    (hbase : 0 < bitWordValue base) (remaining : ℕ)
    (hden : raw.1.value.den ∣ bitWordValue base ^ remaining) :
    (finishCachedWithWork raw base hbase remaining).1.value = raw.1.value :=
  powerDenominatorWithWork_value raw.1 base hbase remaining hden

theorem finishCachedWithWork_bounds (raw : BinaryFraction × ℕ) (base : List Bool)
    (hbase : 0 < bitWordValue base) (remaining A B C V : ℕ)
    (ha : raw.1.width ≤ A) (hb : base.length ≤ B) (hc : raw.2 ≤ C)
    (hden : raw.1.value.den ∣ bitWordValue base ^ remaining) (hv : |raw.1.value| ≤ V) :
    (finishCachedWithWork raw base hbase remaining).1.width ≤
        Nat.size V + 2 * (remaining * B + 1) + 1 ∧
      (finishCachedWithWork raw base hbase remaining).2 ≤
        C + powerDenominatorBitBudget remaining A B + 1 := by
  refine ⟨powerDenominatorWithWork_width raw.1 base hbase remaining V B hb hden hv, ?_⟩
  exact Nat.add_le_add_right (Nat.add_le_add hc
    (powerDenominatorWithWork_cost raw.1 base hbase remaining A B ha hb)) 1

def cachedPhysicalContinuationWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P F : ℕ)
    (delta fallback : BinaryFraction)
    (old current : Fin M × TargetInterval ny → BinaryFraction)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (query : TargetInterval ny) (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ) :
    BinaryFraction × ℕ :=
  finishCachedWithWork
    (physicalContinuationWithWork parent representatives P F delta fallback old current groups online query)
    base hbase remaining

theorem cachedPhysicalContinuationWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P F : ℕ)
    (delta fallback : BinaryFraction)
    (old current : Fin M × TargetInterval ny → BinaryFraction)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (query : TargetInterval ny) (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ)
    (hP : 0 < P)
    (hden : (rationalWideStep parent representatives P (fun _ => fallback.value) (128 * F) delta.value
      (fun s => (old s).value) (fun s => (current s).value)
      (groups.map BinaryBellmanAction.decode) (online.map BinaryBellmanAction.decode) query).den ∣
        bitWordValue base ^ remaining) :
    (cachedPhysicalContinuationWithWork parent representatives P F delta fallback old current groups online
      query base hbase remaining).1.value =
      rationalWideStep parent representatives P (fun _ => fallback.value) (128 * F) delta.value
        (fun s => (old s).value) (fun s => (current s).value)
        (groups.map BinaryBellmanAction.decode) (online.map BinaryBellmanAction.decode) query := by
  apply (finishCachedWithWork_value _ base hbase remaining ?_).trans
    (physicalContinuationWithWork_value parent representatives P F delta fallback old current groups online query hP)
  rwa [physicalContinuationWithWork_value parent representatives P F delta fallback old current groups online query hP]

end BinaryFraction
end EditApproximation

end OAI
