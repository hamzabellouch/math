import OAI.Combinatorics.EditApproximation.Binary.BinaryBandInputWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryAffineGuard

namespace OAI

/-! The warmup mass used in band construction is computed from the gathered
warmup entries by a stored sum and one stored division. -/

namespace EditApproximation
namespace BinaryFraction

def warmupAverageWithWork (values : List BinaryFraction) : BinaryFraction × ℕ :=
  let total := sumListWithWork values
  let result := divWithWork total.1 (nat values.length)
  (result.1, total.2 + result.2 + Nat.size values.length + 2)

@[simp] theorem warmupAverageWithWork_value (values : List BinaryFraction) :
    (warmupAverageWithWork values).1.value = (values.map value).sum / values.length := by
  simp only [warmupAverageWithWork, divWithWork_value, sumListWithWork_value, nat_value]

theorem warmupAverageWithWork_ofFn_value {T : ℕ} (values : Fin T → BinaryFraction) :
    (warmupAverageWithWork (List.ofFn values)).1.value = (∑ i, (values i).value) / T := by
  rw [warmupAverageWithWork_value, List.length_ofFn]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def]

def warmupAverageWordBudget (n B : ℕ) : ℕ :=
  4 * (bandMassTotalStorageBudget n B + Nat.size n + 2) + 4

def warmupAverageBitBudget (n B : ℕ) : ℕ :=
  storedSumBitBudget n B + 6 * n +
    2100 * (bandMassTotalStorageBudget n B + Nat.size n + 4) ^ 2 + Nat.size n + 2

theorem warmupAverageWithWork_bounds (values : List BinaryFraction) (B : ℕ)
    (hv : ∀ v ∈ values, v.width ≤ B) :
    (warmupAverageWithWork values).1.width ≤ warmupAverageWordBudget values.length B ∧
      (warmupAverageWithWork values).2 ≤ warmupAverageBitBudget values.length B := by
  have hs := sumListWithWork_width values B hv
  have hc := sumListWithWork_cost values B hv
  let W := bandMassTotalStorageBudget values.length B + Nat.size values.length + 2
  have hw : (sumListWithWork values).1.width ≤ W := hs.trans (by dsimp only [W]; omega)
  have hn : (nat values.length).width ≤ W := (nat_width_le _).trans (by dsimp only [W]; omega)
  have hd := divWithWork_width_uniform (sumListWithWork values).1 (nat values.length) W hw hn
  have hdc := divWithWork_cost (sumListWithWork values).1 (nat values.length) W hw hn
  refine ⟨hd, ?_⟩
  change (sumListWithWork values).2 + (divWithWork (sumListWithWork values).1 (nat values.length)).2 +
    Nat.size values.length + 2 ≤ _
  unfold warmupAverageBitBudget
  dsimp only [W] at hdc
  simp only [Nat.add_assoc, Nat.reduceAdd] at hdc ⊢
  omega

end BinaryFraction
end EditApproximation

end OAI
