import OAI.Combinatorics.EditApproximation.Queries.QuerySourceKeyWidths
import OAI.Combinatorics.EditApproximation.Queries.QueryOnlineKeyCost

namespace OAI

/-! The source ports are bounded only at keys visited by the adaptive local
loops. Unused natural-number coordinates require no uniform size assumption. -/

namespace EditApproximation.BinaryFraction

theorem queryGroupKeysWithWork_mem_of_guard {n : ℕ} (N F exponent : ℕ)
    (a value : BinaryFraction) (q : TargetInterval n) (eb : ℕ)
    (heb : eb ∈ List.range (max 1 N.bits.length))
    (hg : (refinementScaleGuardWithWork F (2 ^ eb) a value).1 = true)
    (cell : ℕ × ℕ)
    (hc : cell ∈ (targetCellsWithWork
      (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
      (bitWordValue (naturalCeilingWithWork value).1) q).1) :
    (2 ^ eb, cell) ∈ (queryGroupKeysWithWork N F exponent a value q).1 := by
  have he : eb ∈ (queryExponentsWithWork N F a value).1 := by
    simp only [queryExponentsWithWork, filterWithWork_value, List.mem_filter]
    exact ⟨heb, hg⟩
  have hs : 2 ^ eb ∈ (queryScalesWithWork N F a value).1 := by
    simp only [queryScalesWithWork, arithmeticMapWithWork_value, List.mem_map]
    exact ⟨eb, he, powerTwoWord_value eb⟩
  simp only [queryGroupKeysWithWork, arithmeticFlatMapWithWork_value,
    arithmeticMapWithWork_value, List.mem_flatMap, List.mem_map]
  exact ⟨2 ^ eb, hs, cell, hc, rfl⟩

def queryGroupBufferReadBudget (count B V : ℕ) : ℕ :=
  count * (40 * (40 * B + 500) + 15) + 200 * (V + 1) ^ 2 +
    30 * (V + 1) * (V + (40 * B + 500) + 1) + 4

theorem queryGroupDrawReadWithWork_scoped_cost {n M N F Q : ℕ} [NeZero M]
    (exponent eM eF B V : ℕ) (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF)
    (a value : BinaryFraction) (q : TargetInterval n) (words : List BinaryFraction)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hes : 7 + eM + eF ≤ B) (he : exponent + 1 ≤ B)
    (hn : Nat.size n ≤ B) (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value)
    (hV : 2 ≤ V) (hwords : ∀ v ∈ words, v.width ≤ V)
    (eb : ℕ) (heb : eb ∈ List.range (max 1 N.bits.length))
    (hg : (refinementScaleGuardWithWork F (2 ^ eb) a value).1 = true)
    (cell : ℕ × ℕ)
    (hc : cell ∈ (targetCellsWithWork
      (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
      (bitWordValue (naturalCeilingWithWork value).1) q).1)
    (scale : Fin (groupDyadicScales M (2 ^ eb) F).length)
    (sample : Fin (groupSampleCount M Q (2 ^ eb) (groupDyadicScaleAt M (2 ^ eb) F scale))) :
    let keys := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).1
    (queryGroupDrawReadWithWork keys words (2 ^ eb) cell scale sample).2 ≤
      queryGroupBufferReadBudget keys.length B V := by
  dsimp only
  apply queryGroupDrawReadWithWork_cost _ words _ cell scale sample (40 * B + 500) V hV
    (by omega)
    (queryGroupSourceKeysWithWork_width M N F Q exponent eM eF B hMdef hFdef a value q
      hB hN hF hM hes he hn ha hv hw) _ hwords
  apply queryGroupKeySize_bound M N F Q exponent eM eF B hMdef hFdef a value q
    hB hN hF hM hes he hn ha hv hw
  exact queryGroupKeysWithWork_mem_of_guard N F exponent a value q eb heb hg cell hc

theorem queryOnlineKeysWithWork_scale {n : ℕ} (N P F B : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) (hN : Nat.size N ≤ B) (hF : 1 ≤ F)
    (key : ℕ × TargetInterval n) (hk : key ∈ (queryOnlineKeysWithWork N P F hP a value q).1) :
    Nat.size key.1 ≤ B + 1 := by
  simp only [queryOnlineKeysWithWork, arithmeticMapWithWork_value, List.mem_map] at hk
  obtain ⟨b, hb, rfl⟩ := hk
  exact (queryScalesWithWork_member N F B a value hN hF b hb).1

def queryOnlineBufferReadBudget (count B V : ℕ) : ℕ :=
  count * (24 * (B + 1) + 9) + 200 * (V + 1) ^ 2 + 2

theorem queryOnlineIntegerReadWithWork_scoped_cost {n : ℕ} (N P F B V : ℕ)
    (hP : 0 < P) (a value : BinaryFraction) (q : TargetInterval n) (words : List BinaryFraction)
    (hN : Nat.size N ≤ B) (hF : 1 ≤ F) (hn : Nat.size n ≤ B)
    (hV : 2 ≤ V) (hwords : ∀ v ∈ words, v.width ≤ V)
    (e : ℕ) (he : e ∈ (queryExponentsWithWork N F a value).1) :
    let keys := (queryOnlineKeysWithWork N P F hP a value q).1
    let center := (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
      (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1
    (queryOnlineIntegerReadWithWork keys words (2 ^ e) center).2 ≤
      queryOnlineBufferReadBudget keys.length B V := by
  have hs : 2 ^ e ∈ (queryScalesWithWork N F a value).1 := by
    simp only [queryScalesWithWork, arithmeticMapWithWork_value, List.mem_map]
    exact ⟨e, he, powerTwoWord_value e⟩
  apply queryOnlineIntegerReadWithWork_cost _ words _ _ (B + 1) V hV (by omega)
    (queryScalesWithWork_member N F B a value hN hF _ hs).1
    (queryOnlineKeysWithWork_scale N P F B hP a value q hN hF) hwords

end EditApproximation.BinaryFraction

end OAI
