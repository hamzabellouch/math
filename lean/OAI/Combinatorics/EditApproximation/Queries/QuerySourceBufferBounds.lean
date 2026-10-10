import OAI.Combinatorics.EditApproximation.Queries.QueryDataBuffers

namespace OAI

/-! Random-source lookups are charged at the bounded coordinates actually
consumed by the local loops. No bound is assumed on all natural keys. -/

namespace EditApproximation

def queryGroupKeySize {M F Q : ℕ} (key : GroupScalarKey M F Q) : ℕ :=
  Nat.size key.1.1 + Nat.size key.1.2.1 + Nat.size key.1.2.2 +
    Nat.size key.2.1.val + Nat.size key.2.2.val

theorem queryGroupKeyEqualWithWork_cost {M F Q : ℕ}
    (a b : GroupScalarKey M F Q) (B : ℕ)
    (ha : queryGroupKeySize a ≤ B) (hb : queryGroupKeySize b ≤ B) :
    (queryGroupKeyEqualWithWork a b).2 ≤ 40 * B + 14 := by
  unfold queryGroupKeySize at ha hb
  have h1 := naturalEqualWithWork_cost a.1.1 b.1.1 B (by omega) (by omega)
  have h2 := naturalEqualWithWork_cost a.1.2.1 b.1.2.1 B (by omega) (by omega)
  have h3 := naturalEqualWithWork_cost a.1.2.2 b.1.2.2 B (by omega) (by omega)
  have h4 := naturalEqualWithWork_cost a.2.1.val b.2.1.val B (by omega) (by omega)
  have h5 := naturalEqualWithWork_cost a.2.2.val b.2.2.val B (by omega) (by omega)
  change _ + _ + _ + _ + _ + 4 ≤ _
  omega

theorem queryOnlineKeyEqualWithWork_cost {n : ℕ} (a b : ℕ × TargetInterval n)
    (B : ℕ) (ha : Nat.size a.1 ≤ B) (hb : Nat.size b.1 ≤ B) (hn : Nat.size n ≤ B) :
    (queryOnlineKeyEqualWithWork a b).2 ≤ 24 * B + 8 := by
  have hs := naturalEqualWithWork_cost a.1 b.1 B ha hb
  have hi := queryIntervalEqualWithWork_cost a.2 b.2 B hn
  change _ + _ + 1 ≤ _
  omega

namespace BinaryFraction

theorem queryGroupDrawReadWithWork_cost {M F Q : ℕ} [NeZero M]
    (keys : List (GroupScalarKey M F Q)) (values : List BinaryFraction)
    (b : ℕ) (cell : ℕ × ℕ) (scale : Fin (groupDyadicScales M b F).length)
    (sample : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)))
    (B V : ℕ) (hV : 2 ≤ V) (hM : Nat.size M ≤ B)
    (hkeys : ∀ key ∈ keys, queryGroupKeySize key ≤ B)
    (hquery : queryGroupKeySize (⟨(b, cell), scale, sample⟩ : GroupScalarKey M F Q) ≤ B)
    (hvalues : ∀ v ∈ values, v.width ≤ V) :
    (queryGroupDrawReadWithWork keys values b cell scale sample).2 ≤
      keys.length * (40 * B + 15) + 200 * (V + 1) ^ 2 +
        30 * (V + 1) * (V + B + 1) + 4 := by
  let query : GroupScalarKey M F Q := ⟨(b, cell), scale, sample⟩
  let word := gatheredWordLookupWithWork queryGroupKeyEqualWithWork keys values query
  have hl := gatheredWordLookupWithWork_cost_on queryGroupKeyEqualWithWork (40 * B + 14)
    keys values query (fun key hk => queryGroupKeyEqualWithWork_cost query key B hquery (hkeys key hk))
  have hw : word.1.width ≤ V := gatheredWordLookupWithWork_width _ keys values query V hV hvalues
  have hf := naturalFloorWithWork_bounds word.1
  have hs : Nat.size (bitWordValue (naturalFloorWithWork word.1).1) ≤ V :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length _)).trans (hf.1.trans hw)
  have hd := binaryNaturalDivModWithWork_cost (bitWordValue (naturalFloorWithWork word.1).1) M
  have hd' : (binaryNaturalDivModWithWork (bitWordValue (naturalFloorWithWork word.1).1) M).2.2 ≤
      30 * (V + 1) * (V + B + 1) := by
    apply hd.trans
    gcongr
  have hf' : (naturalFloorWithWork word.1).2 ≤ 200 * (V + 1) ^ 2 := by
    apply hf.2.trans
    gcongr
  have hl' : word.2 ≤ 1 + keys.length * (40 * B + 15) := by
    simpa only [word, query, Nat.add_assoc, Nat.reduceAdd] using hl
  change word.2 + (naturalFloorWithWork word.1).2 +
    (binaryNaturalDivModWithWork (bitWordValue (naturalFloorWithWork word.1).1) M).2.2 + 3 ≤ _
  omega

theorem queryOnlineIntegerReadWithWork_cost {n : ℕ}
    (keys : List (ℕ × TargetInterval n)) (values : List BinaryFraction)
    (b : ℕ) (q : TargetInterval n) (B V : ℕ) (hV : 2 ≤ V)
    (hn : Nat.size n ≤ B) (hb : Nat.size b ≤ B)
    (hkeys : ∀ key ∈ keys, Nat.size key.1 ≤ B) (hvalues : ∀ v ∈ values, v.width ≤ V) :
    (queryOnlineIntegerReadWithWork keys values b q).2 ≤
      keys.length * (24 * B + 9) + 200 * (V + 1) ^ 2 + 2 := by
  let word := gatheredWordLookupWithWork queryOnlineKeyEqualWithWork keys values (b, q)
  have hl := gatheredWordLookupWithWork_cost_on queryOnlineKeyEqualWithWork (24 * B + 8)
    keys values (b, q) (fun key hk => queryOnlineKeyEqualWithWork_cost (b, q) key B hb (hkeys key hk) hn)
  have hw : word.1.width ≤ V := gatheredWordLookupWithWork_width _ keys values (b, q) V hV hvalues
  have hf := (naturalFloorWithWork_bounds word.1).2
  have hf' : (naturalFloorWithWork word.1).2 ≤ 200 * (V + 1) ^ 2 := by
    apply hf.trans
    gcongr
  have hl' : word.2 ≤ 1 + keys.length * (24 * B + 9) := by
    simpa only [word, Nat.add_assoc, Nat.reduceAdd] using hl
  change word.2 + (naturalFloorWithWork word.1).2 + 1 ≤ _
  omega

end BinaryFraction
end EditApproximation

end OAI
