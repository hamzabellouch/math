import OAI.Combinatorics.EditApproximation.Queries.QueryCodeBounds
import OAI.Combinatorics.EditApproximation.Queries.QueryScopedOrder

namespace OAI

/-! Word and comparison bounds for the actual finite history-key lists. -/

namespace EditApproximation

theorem queryPairWithWork_bounds (a b B : ℕ) (ha : Nat.size a ≤ B) (hb : Nat.size b ≤ B) :
    Nat.size (queryPairWithWork a b).1 ≤ 5 * (B + 1) ∧
      (queryPairWithWork a b).2 ≤ 10000 * (B + 1) ^ 2 := by
  have haa : Nat.size (a * a) ≤ 3 * B + 1 := by
    have h := queryNaturalMul_size a a
    omega
  have hbb : Nat.size (b * b) ≤ 3 * B + 1 := by
    have h := queryNaturalMul_size b b
    omega
  have hl : Nat.size (a * a + a) ≤ 4 * B + 2 := by
    have h := queryNaturalAdd_size (a * a) a
    omega
  have ho : Nat.size (a * a + a + b) ≤ 5 * B + 3 := by
    have h := queryNaturalAdd_size (a * a + a) b
    omega
  have hp : Nat.size (b * b + a) ≤ 4 * B + 2 := by
    have h := queryNaturalAdd_size (b * b) a
    omega
  let K := 5 * (B + 1)
  have haK : Nat.size a ≤ K := by dsimp [K]; omega
  have hbK : Nat.size b ≤ K := by dsimp [K]; omega
  have haaK : Nat.size (a * a) ≤ K := by dsimp [K]; omega
  have hbbK : Nat.size (b * b) ≤ K := by dsimp [K]; omega
  have hlK : Nat.size (a * a + a) ≤ K := by dsimp [K]; omega
  have ca := queryNaturalMul_cost a a K haK haK
  have cb := queryNaturalMul_cost b b K hbK hbK
  have cl := queryNaturalAdd_cost (a * a) a K haaK haK
  have co := queryNaturalAdd_cost (a * a + a) b K hlK hbK
  have cp := queryNaturalAdd_cost (b * b) a K hbbK haK
  have ct := binaryNaturalCompareWithWork_cost a b
  dsimp only [K] at ca cb cl co cp
  unfold queryPairWithWork
  dsimp only
  split_ifs <;> simp only [binaryNaturalMulWithWork_value, binaryNaturalAddWithWork_value]
  · exact ⟨by omega, by nlinarith only [cb, cp, ct, ha, hb, Nat.zero_le B]⟩
  · exact ⟨by omega, by nlinarith only [ca, cl, co, ct, ha, hb, Nat.zero_le B]⟩

theorem queryHistoryCodeWithWork_bounds {M n : ℕ} (input : Fin M × ℕ × TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) (ht : Nat.size input.2.1 ≤ B) :
    Nat.size (queryHistoryCodeWithWork input).1 ≤ 50 * (B + 1) ∧
      (queryHistoryCodeWithWork input).2 ≤ 1000000 * (B + 1) ^ 2 := by
  have hc := queryChildCodeWithWork_bounds (input.1, input.2.2) B hM hn
  have ht' : Nat.size input.2.1 ≤ 8 * (B + 1) := by omega
  have hp := queryPairWithWork_bounds input.2.1
    (queryChildCodeWithWork (input.1, input.2.2)).1 (8 * (B + 1)) ht' hc.1
  constructor
  · exact hp.1.trans (by omega)
  · change (queryChildCodeWithWork (input.1, input.2.2)).2 +
      (queryPairWithWork input.2.1 (queryChildCodeWithWork (input.1, input.2.2)).1).2 + 1 ≤ _
    nlinarith only [hc.2, hp.2, Nat.zero_le B]

theorem queryHistoryEqualWithWork_cost {M n : ℕ} (a b : Fin M × ℕ × TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B)
    (ha : Nat.size a.2.1 ≤ B) (hb : Nat.size b.2.1 ≤ B) :
    (queryHistoryEqualWithWork a b).2 ≤ 32 * B + 11 := by
  have hc := coordinateEqualWithWork_cost (a.1, a.2.2) (b.1, b.2.2) B hM hn
  have ht := naturalEqualWithWork_cost a.2.1 b.2.1 B ha hb
  change _ + _ + 1 ≤ _
  omega

theorem queryHistoryOrderWithWork_cost {M n : ℕ} (a b : Fin M × ℕ × TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B)
    (ha : Nat.size a.2.1 ≤ B) (hb : Nat.size b.2.1 ≤ B) :
    (queryEncodedLEWithWork queryHistoryCodeWithWork a b).2 ≤ 2001000 * (B + 1) ^ 2 := by
  have ca := queryHistoryCodeWithWork_bounds a B hM hn ha
  have cb := queryHistoryCodeWithWork_bounds b B hM hn hb
  have h := queryEncodedLEWithWork_cost queryHistoryCodeWithWork a b
    (1000000 * (B + 1) ^ 2) (50 * (B + 1)) ca.2 cb.2 ca.1 cb.1
  nlinarith only [h, Nat.zero_le B]

theorem queryOrderedHistoryInputsWithWork_cost {M n : ℕ}
    (inputs : List (Fin M × ℕ × TargetInterval n)) (B : ℕ)
    (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B)
    (ht : ∀ input ∈ inputs, Nat.size input.2.1 ≤ B) :
    (queryOrderedHistoryInputsWithWork inputs).2 ≤
      (inputs.length + 1) ^ 2 * (2002000 * (B + 1) ^ 2) := by
  have h := queryOrderedInputsWithWork_cost_on (fun input : Fin M × ℕ × TargetInterval n =>
      Nat.size input.2.1 ≤ B) historyInputCode queryHistoryEqualWithWork
    (queryEncodedLEWithWork queryHistoryCodeWithWork) queryHistoryEqualWithWork_value
    (fun a b => by simp only [queryEncodedLEWithWork_value, queryHistoryCodeWithWork_value])
    (32 * B + 11) (2001000 * (B + 1) ^ 2)
    (fun a ha b hb => queryHistoryEqualWithWork_cost a b B hM hn ha hb)
    (fun a ha b hb => queryHistoryOrderWithWork_cost a b B hM hn ha hb) inputs ht
  apply h.trans
  gcongr
  nlinarith only [Nat.zero_le B]

end EditApproximation

end OAI
