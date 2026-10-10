import OAI.Combinatorics.EditApproximation.Queries.QueryCellCost

namespace OAI

/-! Size, construction work and coordinate widths of the actual group
key list, including the binary dyadic scale enumeration. -/

namespace EditApproximation.BinaryFraction

def queryGroupKeysBitBudget (F exponent B : ℕ) : ℕ :=
  let L := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  queryScalesBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (queryCellScanBitBudget F exponent B + 5 * L + 5) + exponent + 4

theorem queryGroupKeysWithWork_bounds {n : ℕ} (N F exponent B : ℕ)
    (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hFpos : 1 ≤ F) (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B)
    (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value) :
    (queryGroupKeysWithWork N F exponent a value q).1.length ≤
      (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ∧
    (queryGroupKeysWithWork N F exponent a value q).2 ≤ queryGroupKeysBitBudget F exponent B ∧
    ∀ key ∈ (queryGroupKeysWithWork N F exponent a value q).1,
      Nat.size key.1 ≤ B + 1 ∧ (∃ e : ℕ, key.1 = 2 ^ e) ∧
      Nat.size key.2.1 ≤ 16 * B + 183 ∧ Nat.size key.2.2 ≤ 16 * B + 183 := by
  let scales := queryScalesWithWork N F a value
  let radius := naturalCeilingWithWork value
  let cells := fun b => targetCellsWithWork
    (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).1 (bitWordValue radius.1) q
  let run := fun b =>
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
    let labeled := arithmeticMapWithWork (fun cell => ((b, cell), 1)) (cells b).1
    (labeled.1, side.2 + (cells b).2 + labeled.2 + 2)
  let L := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  have hs := queryScalesWithWork_bounds N F B a value hB hN hF ha hv
  have hc (b : ℕ) (hb : b ∈ scales.1) :
      (cells b).1.length ≤ L ∧
      (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).2 + (cells b).2 ≤
        queryCellScanBitBudget F exponent B ∧
      ∀ cell ∈ (cells b).1, Nat.size cell.1 ≤ 16 * B + 183 ∧ Nat.size cell.2 ≤ 16 * B + 183 := by
    have hm := queryScalesWithWork_member N F B a value hN hFpos b hb
    have hw' := queryScalesWithWork_window N F a value b hb
    have hbp : 1 ≤ b := by obtain ⟨e, rfl⟩ := hw'.1; exact Nat.succ_le_of_lt (Nat.two_pow_pos e)
    exact queryCellScan_bounds F b exponent B value q hFpos hbp hm.1 he hn hv hw hw'.2
  have hlen (b : ℕ) (hb : b ∈ scales.1) : (run b).1.length ≤ L := by
    simpa only [run, arithmeticMapWithWork_value, List.length_map] using (hc b hb).1
  have hwork (b : ℕ) (hb : b ∈ scales.1) :
      (run b).2 ≤ queryCellScanBitBudget F exponent B + 4 * L + 2 := by
    have hm := arithmeticMapWithWork_cost (fun cell => ((b, cell), 1)) (cells b).1 1
      (fun _ _ => le_rfl)
    have hh := hc b hb
    have hm' := hm.trans (Nat.mul_le_mul_right _ hh.1)
    change _ + _ + _ + 2 ≤ _
    simp only [Nat.reduceAdd] at hm'
    rw [Nat.mul_comm L 4] at hm'
    omega
  have hl := (arithmeticFlatMapWithWork_length run scales.1 L hlen).trans
    (Nat.mul_le_mul_right L hs.1)
  have hf := (arithmeticFlatMapWithWork_cost run scales.1
    (queryCellScanBitBudget F exponent B + 4 * L + 2) L hwork hlen).trans
      (Nat.mul_le_mul_right _ hs.1)
  have hrad := (naturalCeilingWithWork_cost value).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right hv 1) 2))
  refine ⟨hl, ?_, ?_⟩
  · change scales.2 + radius.2 + (arithmeticFlatMapWithWork run scales.1).2 + exponent + 4 ≤ _
    change _ ≤ queryScalesBitBudget B + 500 * (B + 1) ^ 2 +
      (B + 1) * (queryCellScanBitBudget F exponent B + 5 * L + 5) + exponent + 4
    rw [show queryCellScanBitBudget F exponent B + 4 * L + 2 + L + 3 =
      queryCellScanBitBudget F exponent B + 5 * L + 5 by omega] at hf
    have hsc : scales.2 ≤ queryScalesBitBudget B := hs.2
    change radius.2 ≤ _ at hrad
    omega
  · intro key hk
    change key ∈ (arithmeticFlatMapWithWork run scales.1).1 at hk
    rw [arithmeticFlatMapWithWork_value] at hk
    obtain ⟨b, hb, hk⟩ := List.mem_flatMap.mp hk
    simp only [run, arithmeticMapWithWork_value] at hk
    obtain ⟨cell, hcell, rfl⟩ := List.mem_map.mp hk
    exact ⟨(queryScalesWithWork_member N F B a value hN hFpos b hb).1,
      (queryScalesWithWork_window N F a value b hb).1, (hc b hb).2.2 cell hcell⟩

end EditApproximation.BinaryFraction

end OAI
