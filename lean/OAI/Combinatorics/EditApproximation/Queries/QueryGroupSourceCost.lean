import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSources
import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSampleCost
import OAI.Combinatorics.EditApproximation.Queries.QueryCellCost

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryExponentsWithWork_member (N F B : ℕ) (a value : BinaryFraction)
    (hN : Nat.size N ≤ B) (eb : ℕ) (heb : eb ∈ (queryExponentsWithWork N F a value).1) :
    eb ≤ B ∧ 2 ^ eb ∈ (queryScalesWithWork N F a value).1 := by
  constructor
  · simp only [queryExponentsWithWork, filterWithWork_value] at heb
    have h := List.mem_range.mp (List.mem_filter.mp heb).1
    rw [Nat.size_eq_bits_len] at h
    omega
  · rw [queryScalesWithWork_value, ← queryExponentsWithWork_value]
    exact List.mem_map.mpr ⟨eb, heb, rfl⟩

def queryGroupSourceKeysLength (M F exponent eM eF B : ℕ) : ℕ :=
  (B + 1) * ((((32 * F + 2) * 2 ^ exponent + 2) ^ 2) * ((7 + eM + eF) * M))

def queryGroupSourceKeysBitBudget (M F exponent eM eF B : ℕ) : ℕ :=
  let cells := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let samples := (7 + eM + eF) * M
  let sampleWork := queryGroupSamplesBitBudget M eM B eF (2 * B + 10)
  let scaleWork := queryCellScanBitBudget F exponent B +
    cells * (sampleWork + samples + 3) + B + exponent + 4
  queryExponentsBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (scaleWork + cells * samples + 3) + 2

theorem queryGroupSourceKeysWithWork_bounds {n : ℕ} (M N F Q exponent eM eF B : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B) (hes : eM + eF + 7 ≤ B)
    (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B) (ha : a.width ≤ B)
    (hv : value.width ≤ B) (hw : 0 ≤ value.value) :
    (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).1.length ≤
      queryGroupSourceKeysLength M F exponent eM eF B ∧
    (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).2 ≤
      queryGroupSourceKeysBitBudget M F exponent eM eF B := by
  let scales := queryExponentsWithWork N F a value
  let radius := naturalCeilingWithWork value
  let cells := fun eb => targetCellsWithWork
    (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1 (bitWordValue radius.1) q
  let sources := fun eb => arithmeticFlatMapWithWork
    (queryGroupKeySamplesWithWork M F Q eM eb eF hMdef hFdef) (cells eb).1
  let run := fun eb =>
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))
    ((sources eb).1, side.2 + (cells eb).2 + (sources eb).2 + eb + exponent + 4)
  let K := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let L := (7 + eM + eF) * M
  let W := queryGroupSamplesBitBudget M eM B eF (2 * B + 10)
  let C := queryCellScanBitBudget F exponent B + K * (W + L + 3) + B + exponent + 4
  have hs := queryExponentsWithWork_bounds N F B a value hB hN hF ha hv
  have hFpos : 1 ≤ F := by rw [hFdef]; exact Nat.succ_le_of_lt (Nat.two_pow_pos _)
  have hrun (eb : ℕ) (heb : eb ∈ scales.1) : (run eb).1.length ≤ K * L ∧ (run eb).2 ≤ C := by
    have hm := queryExponentsWithWork_member N F B a value hN eb heb
    have hwindow := queryScalesWithWork_window N F a value (2 ^ eb) hm.2
    have hcell := queryCellScan_bounds F (2 ^ eb) exponent B value q hFpos
      (Nat.succ_le_of_lt (Nat.two_pow_pos _))
      (by rw [Nat.size_pow]; omega) he hn hv hw hwindow.2
    have hsample (cell : ℕ × ℕ) :
        (queryGroupKeySamplesWithWork M F Q eM eb eF hMdef hFdef cell).1.length ≤ L ∧
        (queryGroupKeySamplesWithWork M F Q eM eb eF hMdef hFdef cell).2 ≤ W := by
      have hh := queryGroupKeySamplesWithWork_bounds M F Q eM eb eF (2 * B + 10)
        hMdef hFdef cell (by omega) (by omega) (by omega) (by omega)
      exact ⟨hh.1, hh.2.trans (queryGroupSamplesBitBudget_mono M eM eb B eF
        (2 * B + 10) (2 * B + 10) hm.1 le_rfl)⟩
    have hl := (arithmeticFlatMapWithWork_length
      (queryGroupKeySamplesWithWork M F Q eM eb eF hMdef hFdef) (cells eb).1 L
      (fun cell _ => (hsample cell).1)).trans (Nat.mul_le_mul_right _ hcell.1)
    have hc := (arithmeticFlatMapWithWork_cost
      (queryGroupKeySamplesWithWork M F Q eM eb eF hMdef hFdef) (cells eb).1 W L
      (fun cell _ => (hsample cell).2) (fun cell _ => (hsample cell).1)).trans
        (Nat.mul_le_mul_right _ hcell.1)
    have hsourcec : (sources eb).2 ≤ K * (W + L + 3) := by
      simpa only [sources] using hc
    have hcellc : (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).2 +
      (cells eb).2 ≤ queryCellScanBitBudget F exponent B := by
      simpa only [cells, radius] using hcell.2.1
    have hcost := Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hcellc hsourcec) hm.1) exponent) 4
    simpa only [run, C] using And.intro hl hcost
  have hl := (arithmeticFlatMapWithWork_length run scales.1 (K * L)
    (fun eb heb => (hrun eb heb).1)).trans (Nat.mul_le_mul_right _ hs.2)
  have hc := (arithmeticFlatMapWithWork_cost run scales.1 C (K * L)
    (fun eb heb => (hrun eb heb).2) (fun eb heb => (hrun eb heb).1)).trans
      (Nat.mul_le_mul_right _ hs.2)
  have hr := (naturalCeilingWithWork_cost value).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right hv 1) 2))
  have hcost := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hs.1 hr) hc) 2
  simpa only [queryGroupSourceKeysWithWork, scales, radius, run, cells, sources,
    queryGroupSourceKeysLength, queryGroupSourceKeysBitBudget, K, L, W, C] using And.intro hl hcost

end EditApproximation.BinaryFraction

end OAI
