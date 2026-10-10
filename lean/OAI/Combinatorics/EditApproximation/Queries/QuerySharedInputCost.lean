import OAI.Combinatorics.EditApproximation.Queries.QuerySharedCellCost
import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSourceCost
import OAI.Combinatorics.EditApproximation.Queries.QueryActionInputCost

namespace OAI

namespace EditApproximation.BinaryFraction

def querySharedInputsLength (M F exponent eM eF B : ℕ) : ℕ :=
  (B + 1) * ((((32 * F + 2) * 2 ^ exponent + 2) ^ 2) * querySharedCellInputsLength M exponent eM eF)

def querySharedInputsBitBudget (M F exponent eM eF B R : ℕ) : ℕ :=
  let cells := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let samples := querySharedCellInputsLength M exponent eM eF
  let sampleWork := querySharedCellInputsBitBudget M exponent eM B eF (16 * B + 200) R
  let scaleWork := queryCellScanBitBudget F exponent B +
    cells * (sampleWork + samples + 3) + B + exponent + 4
  queryExponentsBitBudget B + 500 * (B + 1) ^ 2 + (B + 1) * (scaleWork + cells * samples + 3) +
    (querySharedInputsLength M F exponent eM eF B + 1) ^ 2 * (202000 * (B + 1) ^ 2) + 3

theorem querySharedInputsWithWork_bounds_on {nx ny : ℕ} (M N F Q exponent eM eF B R : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (parent : TargetInterval nx)
    (a value : BinaryFraction) (q : TargetInterval ny) (draw : CountedCellGroupDraws M F Q)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B) (hes : eM + eF + 7 ≤ B)
    (he : exponent + 1 ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value)
    (hR : ∀ eb ∈ (queryExponentsWithWork N F a value).1,
      ∀ cell ∈ (targetCellsWithWork
        (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
        (bitWordValue (naturalCeilingWithWork value).1) q).1,
      ∀ scale sample, (draw (2 ^ eb) cell scale sample).2 ≤ R) :
    (querySharedInputsWithWork M N F Q exponent eM eF hMdef hFdef parent a value q draw).1.length ≤
      querySharedInputsLength M F exponent eM eF B ∧
    (querySharedInputsWithWork M N F Q exponent eM eF hMdef hFdef parent a value q draw).2 ≤
      querySharedInputsBitBudget M F exponent eM eF B R := by
  let scales := queryExponentsWithWork N F a value
  let radius := naturalCeilingWithWork value
  let cells := fun eb => targetCellsWithWork
    (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1 (bitWordValue radius.1) q
  let sources := fun eb => arithmeticFlatMapWithWork (fun cell =>
    querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hMdef hFdef parent exponent cell (draw (2 ^ eb) cell)) (cells eb).1
  let run := fun eb =>
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))
    ((sources eb).1, side.2 + (cells eb).2 + (sources eb).2 + eb + exponent + 4)
  let K := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let L := querySharedCellInputsLength M exponent eM eF
  let W := querySharedCellInputsBitBudget M exponent eM B eF (16 * B + 200) R
  let C := queryCellScanBitBudget F exponent B + K * (W + L + 3) + B + exponent + 4
  let raw := arithmeticFlatMapWithWork run scales.1
  have hs := queryExponentsWithWork_bounds N F B a value hB hN hF ha hv
  have hFpos : 1 ≤ F := by rw [hFdef]; exact Nat.succ_le_of_lt (Nat.two_pow_pos _)
  have hrun (eb : ℕ) (heb : eb ∈ scales.1) : (run eb).1.length ≤ K * L ∧ (run eb).2 ≤ C := by
    have hm := queryExponentsWithWork_member N F B a value hN eb heb
    have hwindow := queryScalesWithWork_window N F a value (2 ^ eb) hm.2
    have hcell := queryCellScan_bounds F (2 ^ eb) exponent B value q hFpos
      (Nat.succ_le_of_lt (Nat.two_pow_pos _)) (by rw [Nat.size_pow]; omega) he hny hv hw hwindow.2
    have hsample (cell : ℕ × ℕ) (hc : cell ∈ (cells eb).1) :
        (querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hMdef hFdef parent exponent cell
          (draw (2 ^ eb) cell)).1.length ≤ L ∧
        (querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hMdef hFdef parent exponent cell
          (draw (2 ^ eb) cell)).2 ≤ W := by
      have hcoord := hcell.2.2 cell hc
      have hh := querySharedCellInputsWithWork_bounds (ny := ny) M F Q eM eb eF hMdef hFdef parent
        exponent (16 * B + 200) R cell (draw (2 ^ eb) cell)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (hR eb heb cell hc)
      exact ⟨hh.1, hh.2.trans (querySharedCellInputsBitBudget_mono_eb M exponent eM eb B eF
        (16 * B + 200) R hm.1)⟩
    have hl := (arithmeticFlatMapWithWork_length _ (cells eb).1 L
      (fun cell hc => (hsample cell hc).1)).trans (Nat.mul_le_mul_right _ hcell.1)
    have hc := (arithmeticFlatMapWithWork_cost _ (cells eb).1 W L
      (fun cell hc => (hsample cell hc).2) (fun cell hc => (hsample cell hc).1)).trans
        (Nat.mul_le_mul_right _ hcell.1)
    have hsourceCost : (sources eb).2 ≤ K * (W + L + 3) := by
      simpa only [sources, K] using hc
    have hcellCost : (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).2 +
        (cells eb).2 ≤ queryCellScanBitBudget F exponent B := by
      simpa only [cells, radius] using hcell.2.1
    have hrunCost : (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).2 +
        (cells eb).2 + (sources eb).2 + eb + exponent + 4 ≤ C := by
      simpa only [C] using Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hcellCost hsourceCost) hm.1) exponent) 4
    simpa only [run, sources] using And.intro hl hrunCost
  have hl := (arithmeticFlatMapWithWork_length run scales.1 (K * L)
    (fun eb heb => (hrun eb heb).1)).trans (Nat.mul_le_mul_right _ hs.2)
  have hc := (arithmeticFlatMapWithWork_cost run scales.1 C (K * L)
    (fun eb heb => (hrun eb heb).2) (fun eb heb => (hrun eb heb).1)).trans
      (Nat.mul_le_mul_right _ hs.2)
  have hr := (naturalCeilingWithWork_cost value).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right hv 1) 2))
  have hsort := (queryOrderedChildInputsWithWork_cost raw.1 B (by omega) hny).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.add_le_add_right hl 1) 2))
  have hlength := (queryOrderedChildInputsWithWork_length raw.1).trans hl
  have hsc : scales.2 ≤ queryExponentsBitBudget B := hs.1
  have hradius : radius.2 ≤ 500 * (B + 1) ^ 2 := by
    simpa only [radius] using hr
  have hraw : raw.2 ≤ (B + 1) * (C + K * L + 3) := by
    simpa only [raw] using hc
  have hcost : scales.2 + radius.2 + raw.2 + (queryOrderedChildInputsWithWork raw.1).2 + 3 ≤
      querySharedInputsBitBudget M F exponent eM eF B R := by
    simpa only [querySharedInputsBitBudget, querySharedInputsLength, C, K, L, W] using
      Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hsc hradius) hraw) hsort) 3
  simpa only [querySharedInputsWithWork, scales, radius, cells, sources, run, raw,
    querySharedInputsLength, K, L] using And.intro hlength hcost


theorem querySharedInputsWithWork_bounds {nx ny : ℕ} (M N F Q exponent eM eF B R : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (parent : TargetInterval nx)
    (a value : BinaryFraction) (q : TargetInterval ny) (draw : CountedCellGroupDraws M F Q)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B) (hes : eM + eF + 7 ≤ B)
    (he : exponent + 1 ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value)
    (hR : ∀ b cell scale sample, (draw b cell scale sample).2 ≤ R) :
    (querySharedInputsWithWork M N F Q exponent eM eF hMdef hFdef parent a value q draw).1.length ≤
      querySharedInputsLength M F exponent eM eF B ∧
    (querySharedInputsWithWork M N F Q exponent eM eF hMdef hFdef parent a value q draw).2 ≤
      querySharedInputsBitBudget M F exponent eM eF B R :=
  querySharedInputsWithWork_bounds_on M N F Q exponent eM eF B R hMdef hFdef parent a value q draw
    hB hN hF hM hQ hes he hnx hny ha hv hw (fun eb _ cell _ => hR (2 ^ eb) cell)

end EditApproximation.BinaryFraction

end OAI
