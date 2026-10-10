import OAI.Combinatorics.EditApproximation.Queries.QueryRawCenterCost
import OAI.Combinatorics.EditApproximation.Binary.BinaryCellCentersWork

namespace OAI

/-! Uniform bounds for the actual cell scan at an accepted query scale.
The scale-window test controls its count; the binary arithmetic controls
its coordinate widths independently of the numeric target length. -/

namespace EditApproximation.BinaryFraction

theorem queryCellCoordinates_count (F b exponent p : ℕ) (w : ℚ)
    (hF : 1 ≤ F) (hb : 1 ≤ b) (hw : 0 ≤ w) (hwindow : w / (16 * F) ≤ b) :
    (localCellCoordinates ((2 : ℚ) ^ (-(exponent : ℤ)) * b) p ⌈w⌉₊).length ≤
      (32 * F + 2) * 2 ^ exponent + 2 := by
  have hbR : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have hs : 0 < (2 : ℚ) ^ (-(exponent : ℤ)) * b := by
    have hbp : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
    positivity
  apply localCellCoordinates_length_le _ hs _ _ ((32 * F + 2) * 2 ^ exponent)
  apply (div_le_iff₀ hs).2
  have hw' : w ≤ 16 * (F : ℚ) * b := by
    have hf : (0 : ℚ) < F := by exact_mod_cast (show 0 < F by omega)
    nlinarith only [(div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hwindow]
  have hc : (⌈w⌉₊ : ℚ) < w + 1 := Nat.ceil_lt_add_one hw
  have heq : (((32 * F + 2) * 2 ^ exponent : ℕ) : ℚ) *
      ((2 : ℚ) ^ (-(exponent : ℤ)) * b) = (32 * (F : ℚ) + 2) * b := by
    push_cast
    rw [zpow_neg, zpow_natCast]
    field_simp
  rw [heq]
  nlinarith only [hc, hw', hbR]

theorem queryScalesWithWork_window (N F : ℕ) (a value : BinaryFraction) (b : ℕ)
    (hb : b ∈ (queryScalesWithWork N F a value).1) :
    (∃ e : ℕ, b = 2 ^ e) ∧ value.value / (16 * F) ≤ b := by
  rw [queryScalesWithWork_value] at hb
  obtain ⟨hd, hg⟩ := List.mem_filter.mp hb
  refine ⟨?_, (of_decide_eq_true hg).1⟩
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hd
  exact ⟨e, rfl⟩

def queryCellScanBitBudget (F exponent B : ℕ) : ℕ :=
  let K := (32 * F + 2) * 2 ^ exponent + 2
  2000 * (B + 4) ^ 2 + targetCellsBitBudget K K (4 * B + 40)

theorem queryCellScan_bounds {n : ℕ} (F b exponent B : ℕ)
    (value : BinaryFraction) (q : TargetInterval n)
    (hF : 1 ≤ F) (hb : 1 ≤ b) (hbs : Nat.size b ≤ B + 1)
    (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B) (hv : value.width ≤ B)
    (hw : 0 ≤ value.value) (hwindow : value.value / (16 * F) ≤ b) :
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
    let radius := naturalCeilingWithWork value
    let cells := targetCellsWithWork side.1 (bitWordValue radius.1) q
    cells.1.length ≤ ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ∧
    side.2 + cells.2 ≤ queryCellScanBitBudget F exponent B ∧
    ∀ cell ∈ cells.1, Nat.size cell.1 ≤ 16 * B + 183 ∧ Nat.size cell.2 ≤ 16 * B + 183 := by
  let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
  let radius := naturalCeilingWithWork value
  let cells := targetCellsWithWork side.1 (bitWordValue radius.1) q
  let K := (32 * F + 2) * 2 ^ exponent + 2
  have htheta : (inversePowerTwo exponent).width ≤ B := by rw [inversePowerTwo_width]; exact he
  have hbn : (nat b).width ≤ B + 3 := (nat_width_le b).trans (by omega)
  have hsw := canonicalMulWithWork_width (inversePowerTwo exponent) (nat b) (B + 3) (by omega) hbn
  have hsc := canonicalMulWithWork_cost (inversePowerTwo exponent) (nat b) (B + 3) (by omega) hbn
  have hrw : Nat.size (bitWordValue radius.1) ≤ B + 2 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length radius.1)).trans
      ((naturalCeilingWithWork_length value).trans (by omega))
  have hcoords (p : ℕ) : (localCellCoordinates side.1.value p (bitWordValue radius.1)).length ≤ K := by
    simp only [side, canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
      radius, naturalCeilingWithWork_value]
    exact queryCellCoordinates_count F b exponent p value.value hF hb hw hwindow
  have hcc := targetCellsWithWork_cost side.1 (bitWordValue radius.1) (4 * B + 40)
    q (by change side.1.width ≤ _ at hsw; omega) (by omega) (by omega)
  have hcells : cells.2 ≤ targetCellsBitBudget K K (4 * B + 40) := hcc.trans (by
    unfold targetCellsBitBudget
    gcongr <;> apply hcoords)
  refine ⟨?_, ?_, ?_⟩
  · rw [targetCellsWithWork_value]
    simp only [canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
      naturalCeilingWithWork_value]
    exact localTargetCells_query_length F b exponent q value.value hF hb hw hwindow
  · change side.2 + cells.2 ≤ _
    change side.2 ≤ _ at hsc
    exact Nat.add_le_add hsc hcells
  · intro cell hc
    have hk := targetCellsWithWork_keys side.1 (bitWordValue radius.1) (4 * B + 40) q
      (by change side.1.width ≤ _ at hsw; omega) (by omega) (by omega) cell hc
    constructor <;> omega

end EditApproximation.BinaryFraction

end OAI
