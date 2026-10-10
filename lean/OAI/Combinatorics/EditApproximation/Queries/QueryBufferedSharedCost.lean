import OAI.Combinatorics.EditApproximation.Queries.QueryScopedSourceCost
import OAI.Combinatorics.EditApproximation.Queries.QuerySharedInputCost

namespace OAI

/-! Shared-state generation using the actual gathered scalar buffer.
The lookup bound is instantiated at visited keys, including discarded cells. -/

namespace EditApproximation.BinaryFraction

def queryBufferedGroupReadBudget (M F exponent eM eF B V : ℕ) : ℕ :=
  queryGroupBufferReadBudget (queryGroupSourceKeysLength M F exponent eM eF B) B V

theorem querySharedInputsWithWork_buffered_bounds {nx ny M N F Q : ℕ} [NeZero M]
    (exponent eM eF B V : ℕ) (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF)
    (parent : TargetInterval nx) (a value : BinaryFraction) (q : TargetInterval ny)
    (words : List BinaryFraction)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B) (hes : eM + eF + 7 ≤ B)
    (he : exponent + 1 ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value)
    (hV : 2 ≤ V) (hwords : ∀ v ∈ words, v.width ≤ V) :
    let keys := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).1
    let result := querySharedInputsWithWork M N F Q exponent eM eF hMdef hFdef parent a value q
      (queryGroupDrawReadWithWork keys words)
    result.1.length ≤ querySharedInputsLength M F exponent eM eF B ∧
    result.2 ≤ querySharedInputsBitBudget M F exponent eM eF B
      (queryBufferedGroupReadBudget M F exponent eM eF B V) := by
  have hk := (queryGroupSourceKeysWithWork_bounds M N F Q exponent eM eF B hMdef hFdef a value q
    hB hN hF hM hQ hes he hny ha hv hw).1
  apply querySharedInputsWithWork_bounds_on M N F Q exponent eM eF B
    (queryBufferedGroupReadBudget M F exponent eM eF B V) hMdef hFdef parent a value q
    (queryGroupDrawReadWithWork _ words) hB hN hF hM hQ hes he hnx hny ha hv hw
  intro eb heb cell hcell scale sample
  have hguard : (refinementScaleGuardWithWork F (2 ^ eb) a value).1 = true := by
    have h := heb
    simp only [queryExponentsWithWork, filterWithWork_value, List.mem_filter] at h
    exact h.2
  have hrange : eb ∈ List.range (max 1 N.bits.length) := by
    have h := heb
    simp only [queryExponentsWithWork, filterWithWork_value, List.mem_filter] at h
    exact h.1
  have hc := queryGroupDrawReadWithWork_scoped_cost exponent eM eF B V hMdef hFdef a value q words
    hB hN hF (by omega) (by omega) he hny ha hv hw hV hwords eb hrange hguard cell hcell scale sample
  apply hc.trans
  unfold queryBufferedGroupReadBudget queryGroupBufferReadBudget
  gcongr

end EditApproximation.BinaryFraction

end OAI
