import OAI.Combinatorics.EditApproximation.Queries.QueryBufferedSharedCost

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryBufferedGroupReadCost {n M N F Q : ℕ} [NeZero M]
    (exponent eM eF B V : ℕ) (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF)
    (a value : BinaryFraction) (q : TargetInterval n) (words : List BinaryFraction)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B) (hes : eM + eF + 7 ≤ B)
    (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B) (ha : a.width ≤ B)
    (hv : value.width ≤ B) (hw : 0 ≤ value.value) (hV : 2 ≤ V)
    (hwords : ∀ v ∈ words, v.width ≤ V) :
    let keys := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).1
    ∀ eb ∈ List.range (max 1 N.bits.length),
      (refinementScaleGuardWithWork F (2 ^ eb) a value).1 = true →
      ∀ cell ∈ (targetCellsWithWork
        (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
        (bitWordValue (naturalCeilingWithWork value).1) q).1,
      ∀ scale sample, (queryGroupDrawReadWithWork keys words (2 ^ eb) cell scale sample).2 ≤
        queryBufferedGroupReadBudget M F exponent eM eF B V := by
  dsimp only
  intro eb heb hg cell hc scale sample
  have hk := (queryGroupSourceKeysWithWork_bounds M N F Q exponent eM eF B hMdef hFdef a value q
    hB hN hF hM hQ hes he hn ha hv hw).1
  have hr := queryGroupDrawReadWithWork_scoped_cost exponent eM eF B V hMdef hFdef a value q words
    hB hN hF (by omega) (by omega) he hn ha hv hw hV hwords eb heb hg cell hc scale sample
  apply hr.trans
  unfold queryBufferedGroupReadBudget queryGroupBufferReadBudget
  gcongr

theorem queryBufferedOnlineReadCost {n : ℕ} (N P F B V : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) (words : List BinaryFraction)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hn : Nat.size n ≤ B) (ha : a.width ≤ B) (hv : value.width ≤ B)
    (hV : 2 ≤ V) (hwords : ∀ v ∈ words, v.width ≤ V) :
    let keys := (queryOnlineKeysWithWork N P F hP a value q).1
    ∀ e ∈ (queryExponentsWithWork N F a value).1,
      (queryOnlineIntegerReadWithWork keys words (2 ^ e)
        (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).2 ≤
        queryOnlineBufferReadBudget (B + 1) B V := by
  dsimp only
  intro e he
  have hk := (queryOnlineKeysWithWork_bounds N P F B hP a value q hB hN hF hFpos hPb hn ha hv).1
  have hr := queryOnlineIntegerReadWithWork_scoped_cost N P F B V hP a value q words
    hN hFpos hn hV hwords e he
  apply hr.trans
  unfold queryOnlineBufferReadBudget
  gcongr

theorem queryOnlineIntegerReadWithWork_size {n : ℕ}
    (keys : List (ℕ × TargetInterval n)) (words : List BinaryFraction) (b : ℕ) (q : TargetInterval n)
    (V : ℕ) (hV : 2 ≤ V) (hwords : ∀ v ∈ words, v.width ≤ V) :
    Nat.size (queryOnlineIntegerReadWithWork keys words b q).1 ≤ V := by
  let word := gatheredWordLookupWithWork queryOnlineKeyEqualWithWork keys words (b, q)
  have hw : word.1.width ≤ V := gatheredWordLookupWithWork_width _ keys words _ V hV hwords
  have hf := (naturalFloorWithWork_bounds word.1).1
  change Nat.size (bitWordValue (naturalFloorWithWork word.1).1) ≤ V
  exact (Nat.size_le.mpr (bitWordValue_lt_pow_length _)).trans (hf.trans hw)

end EditApproximation.BinaryFraction

end OAI
