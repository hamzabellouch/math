import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedLocalGroups
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedComputedCellWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalRepresentativeWork

namespace OAI

/-! Bit work of the literal query-local whole-cell loops.  The tested scale
inequality bounds both coordinate ranges; every generated cell invokes the
complete counted band and sampled-action routine. -/

namespace EditApproximation
namespace BinaryFraction

private theorem queryCellCoordinates_length (F b exponent p : ℕ) (w : ℚ)
    (hF : 1 ≤ F) (hb : 1 ≤ b) (hw : 0 ≤ w) (hwindow : w / (16 * F) ≤ b) :
    (localCellCoordinates ((2 : ℚ) ^ (-(exponent : ℤ)) * b) p ⌈w⌉₊).length ≤
      (32 * F + 2) * 2 ^ exponent + 2 := by
  have hFp : (0 : ℚ) < F := by exact_mod_cast (show 0 < F by omega)
  have hbp : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
  have hbR : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have hs : 0 < (2 : ℚ) ^ (-(exponent : ℤ)) * b := by positivity
  apply localCellCoordinates_length_le _ hs _ _ ((32 * F + 2) * 2 ^ exponent)
  apply (div_le_iff₀ hs).2
  have hw' : w ≤ 16 * (F : ℚ) * b := by
    nlinarith only [(div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hwindow]
  have hc : (⌈w⌉₊ : ℚ) < w + 1 := Nat.ceil_lt_add_one hw
  have heq : (((32 * F + 2) * 2 ^ exponent : ℕ) : ℚ) *
      ((2 : ℚ) ^ (-(exponent : ℤ)) * b) = (32 * (F : ℚ) + 2) * b := by
    push_cast
    rw [zpow_neg, zpow_natCast]
    field_simp
  rw [heq]
  nlinarith only [hc, hw', hbR]

def preparedLocalGroupScaleBitBudget (M P F exponent eM eF eb B : ℕ) : ℕ :=
  let K := (32 * F + 2) * 2 ^ exponent + 2
  let C := 16 * B + 200
  2000 * (B + 4) ^ 2 + 500 * (B + 1) ^ 2 +
    targetCellsBitBudget K K (4 * B + 40) +
    K ^ 2 * (groupScalesBitBudget eM eb eF +
      preparedCellGroupBitBudget M (7 + eM + eF) exponent (2 ^ eb) P C + 4) + eb + 4

theorem preparedLocalGroupScaleWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent Q eM eF eb B : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (hPpos : 0 < P)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hB : 7 ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hM : Nat.size M + 2 ≤ B)
    (hQ : Nat.size Q + 2 ≤ B) (hP : Nat.size P ≤ B)
    (hF : Nat.size F + 2 ≤ B) (he : exponent + 1 ≤ B) (heb : eb ≤ B)
    (hes : eM + eF + 7 ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B)
    (hparent : ∀ q, (parentInitial q).width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B)
    (hinitial : ∀ i q, (initial i q).width ≤ B)
    (hcurrent : ∀ i q, (current i q).width ≤ B)
    (hnonneg : 0 ≤ (parentInitial query).value)
    (hwindow : (parentInitial query).value / (16 * F) ≤ (2 ^ eb : ℕ))
    (hPdyadic : ∃ j : ℕ, P = 2 ^ j) :
    (preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb
      hMdef hFdef hPpos tau a parentInitial child initial current draw query).2 ≤
      preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B := by
  let b := 2 ^ eb
  let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
  let radius := naturalCeilingWithWork (parentInitial query)
  let cells := targetCellsWithWork side.1 (bitWordValue radius.1) query
  let K := (32 * F + 2) * 2 ^ exponent + 2
  let C := 16 * B + 200
  have htheta : (inversePowerTwo exponent).width ≤ B :=
    by rw [inversePowerTwo_width]; exact he
  have hb : Nat.size b + 2 ≤ B + 3 := by dsimp only [b]; rw [Nat.size_pow]; omega
  have hbn : (nat b).width ≤ B + 3 := (nat_width_le b).trans hb
  have hsw := canonicalMulWithWork_width (inversePowerTwo exponent) (nat b) (B + 3)
    (by omega) hbn
  have hsc := canonicalMulWithWork_cost (inversePowerTwo exponent) (nat b) (B + 3)
    (by omega) hbn
  have hrw : Nat.size (bitWordValue radius.1) ≤ B + 2 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length radius.1)).trans
      ((naturalCeilingWithWork_length (parentInitial query)).trans (by have hh := hparent query; omega))
  have hrc := (naturalCeilingWithWork_cost (parentInitial query)).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right (hparent query) 1) 2))
  have hcoords (p : ℕ) : (localCellCoordinates side.1.value p (bitWordValue radius.1)).length ≤ K := by
    simp only [side, canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
      radius, naturalCeilingWithWork_value]
    exact queryCellCoordinates_length F b exponent p (parentInitial query).value
      (by rw [hFdef]; exact Nat.succ_le_of_lt (Nat.two_pow_pos _))
      (Nat.succ_le_of_lt (Nat.two_pow_pos _)) hnonneg hwindow
  have hcc := targetCellsWithWork_cost side.1 (bitWordValue radius.1) (4 * B + 40)
    query (by change side.1.width ≤ _ at hsw; omega)
    (by omega) (by omega)
  have hcells : cells.2 ≤ targetCellsBitBudget K K (4 * B + 40) := hcc.trans (by
    unfold targetCellsBitBudget
    gcongr <;> apply hcoords)
  have hlen : cells.1.length ≤ K ^ 2 := by
    rw [targetCellsWithWork_value]
    simp only [side, canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
      radius, naturalCeilingWithWork_value]
    exact localTargetCells_query_length F b exponent query (parentInitial query).value
      (by rw [hFdef]; exact Nat.succ_le_of_lt (Nat.two_pow_pos _))
      (Nat.succ_le_of_lt (Nat.two_pow_pos _)) hnonneg hwindow
  have hslen : (groupDyadicScales M b (nat F).value).length = 7 + eM + eF := by
    have hh := computedGroupScales_value M b F eM eb eF hMdef rfl hFdef
    have hlen' := congrArg List.length hh
    rw [List.length_map, groupScalesWithWork_length] at hlen'
    exact hlen'.symm
  have hcell (cell : ℕ × ℕ) (hc : cell ∈ cells.1) :=
    targetCellsWithWork_keys side.1 (bitWordValue radius.1) (4 * B + 40) query
      (by change side.1.width ≤ _ at hsw; omega)
      (by omega) (by omega) cell hc
  have hentry (cell : ℕ × ℕ) (hc : cell ∈ cells.1) :
      (preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF
        hMdef rfl hFdef hPpos tau a parentInitial child initial current
        (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (draw b cell)) cell).2 ≤
      groupScalesBitBudget eM eb eF +
        preparedCellGroupBitBudget M (7 + eM + eF) exponent b P C + 1 := by
    have hk := hcell cell hc
    have hh := preparedComputedCellGroupWithWork_cost source target parent b P F exponent Q eM eb eF C
      hMdef rfl hFdef hPpos tau a parentInitial child initial current
      (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (draw b cell)) cell
      (by dsimp only [C]; omega) (by dsimp only [C]; omega) (by dsimp only [C]; omega)
      (by dsimp only [C]; omega) (by dsimp only [C]; omega) (by dsimp only [C]; omega)
      (by dsimp only [C]; omega) (by dsimp only [C]; omega) (by dsimp only [C]; omega)
      (htau.trans (by dsimp only [C]; omega)) (ha.trans (by dsimp only [C]; omega))
      (fun q => (hparent q).trans (by dsimp only [C]; omega))
      (fun i q => (hchild i q).trans (by dsimp only [C]; omega))
      (fun i q => (hinitial i q).trans (by dsimp only [C]; omega))
      (fun i q => (hcurrent i q).trans (by dsimp only [C]; omega))
      (by dsimp only [C]; omega) (by dsimp only [C]; omega) (by dsimp only [C]; omega) hPdyadic
    simpa only [hslen] using hh
  have hfilter := filterMapWithWork_cost (fun cell =>
    preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF
      hMdef rfl hFdef hPpos tau a parentInitial child initial current
      (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (draw b cell)) cell)
    cells.1 (groupScalesBitBudget eM eb eF +
      preparedCellGroupBitBudget M (7 + eM + eF) exponent b P C + 1) hentry
  have hf := hfilter.trans (Nat.mul_le_mul_right _ hlen)
  change side.2 + radius.2 + cells.2 +
    (filterMapWithWork (fun cell =>
      preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF
        hMdef rfl hFdef hPpos tau a parentInitial child initial current
        (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (draw b cell)) cell) cells.1).2 + eb + 4 ≤ _
  change side.2 ≤ _ at hsc
  change radius.2 ≤ _ at hrc
  unfold preparedLocalGroupScaleBitBudget
  change _ ≤ 2000 * (B + 4) ^ 2 + 500 * (B + 1) ^ 2 +
    targetCellsBitBudget K K (4 * B + 40) + K ^ 2 *
      (groupScalesBitBudget eM eb eF + preparedCellGroupBitBudget M (7 + eM + eF) exponent b P C + 4) + eb + 4
  simp only [Nat.add_assoc, Nat.reduceAdd] at hsc hf ⊢
  omega

private theorem flatMap_cost_sum {α β : Type*} (f : α → List β × ℕ)
    (xs : List α) (C L : α → ℕ)
    (hc : ∀ x ∈ xs, (f x).2 ≤ C x) (hl : ∀ x ∈ xs, (f x).1.length ≤ L x) :
    (arithmeticFlatMapWithWork f xs).2 ≤ (xs.map (fun x => C x + L x + 3)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := hc x (by simp)
    have hxl := hl x (by simp)
    have ht := ih (fun y hy => hc y (by simp [hy])) (fun y hy => hl y (by simp [hy]))
    simp only [arithmeticFlatMapWithWork, List.map_cons, List.sum_cons]
    omega

def preparedLocalGroupsBitBudget (N M P F exponent eM eF B : ℕ) : ℕ :=
  let count := max 1 N.bits.length
  let cells := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  ((List.range count).map fun eb => localEligibilityBitBudget (B + 3) +
    preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B + eb + 4 + cells + 3).sum +
    count + N.bits.length + 2

theorem preparedLocalCellGroupsWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q eM eF B : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (hPpos : 0 < P)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hM : Nat.size M + 2 ≤ B)
    (hQ : Nat.size Q + 2 ≤ B) (hP : Nat.size P ≤ B)
    (hF : Nat.size F + 2 ≤ B) (he : exponent + 1 ≤ B) (hes : eM + eF + 7 ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B)
    (hparent : ∀ q, (parentInitial q).width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B)
    (hinitial : ∀ i q, (initial i q).width ≤ B)
    (hcurrent : ∀ i q, (current i q).width ≤ B)
    (hnonneg : 0 ≤ (parentInitial query).value)
    (hPdyadic : ∃ j : ℕ, P = 2 ^ j) :
    (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF
      hMdef hFdef hPpos tau a parentInitial child initial current draw query).2 ≤
      preparedLocalGroupsBitBudget N M P F exponent eM eF B := by
  let count := max 1 N.bits.length
  let K := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let callback := fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query)
    if guard.1 then
      let selected := preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb
        hMdef hFdef hPpos tau a parentInitial child initial current draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)
  have heb (eb : ℕ) (hh : eb ∈ List.range count) : eb ≤ B := by
    have hh' := List.mem_range.mp hh
    dsimp only [count] at hh'
    rw [Nat.size_eq_bits_len] at hh'
    omega
  have hcallback (eb : ℕ) (hh : eb ∈ List.range count) :
      (callback eb).2 ≤ localEligibilityBitBudget (B + 3) +
        preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B + eb + 4 ∧
      (callback eb).1.length ≤ K := by
    have he' := heb eb hh
    have hguard := refinementScaleGuardWithWork_cost F (2 ^ eb) (B + 3) a (parentInitial query)
      (hB.trans (Nat.le_add_right B 3)) (by rw [Nat.size_pow]; omega)
      (hF.trans (Nat.le_add_right B 3)) (ha.trans (Nat.le_add_right B 3))
      ((hparent query).trans (Nat.le_add_right B 3))
    dsimp only [callback]
    split_ifs with hg
    · have hwindow := ((refinementScaleGuardWithWork_value F (2 ^ eb) a (parentInitial query)).mp hg).1
      have hscale := preparedLocalGroupScaleWithWork_cost source target parent P F exponent Q eM eF eb B
        hMdef hFdef hPpos tau a parentInitial child initial current draw query
        hB hnx hny hM hQ hP hF he he' hes htau ha hparent hchild hinitial hcurrent hnonneg hwindow hPdyadic
      have hlen : (preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb
          hMdef hFdef hPpos tau a parentInitial child initial current draw query).1.length ≤ K := by
        unfold preparedLocalGroupScaleWithWork
        rw [filterMapWithWork_value]
        apply (List.length_filterMap_le _ _).trans
        rw [targetCellsWithWork_value]
        simp only [canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
          naturalCeilingWithWork_value]
        exact localTargetCells_query_length F (2 ^ eb) exponent query (parentInitial query).value
          (by rw [hFdef]; exact Nat.succ_le_of_lt (Nat.two_pow_pos _))
          (Nat.succ_le_of_lt (Nat.two_pow_pos _)) hnonneg hwindow
      have hcost := Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add hguard hscale) eb) 4
      simpa only using And.intro hcost hlen
    · have hcost := Nat.add_le_add_right (Nat.add_le_add_right
        (hguard.trans (Nat.le_add_right (localEligibilityBitBudget (B + 3))
          (preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B))) eb) 4
      simpa only [List.length_nil] using And.intro hcost (Nat.zero_le K)
  have hsum := flatMap_cost_sum callback (List.range count)
    (fun eb => localEligibilityBitBudget (B + 3) +
      preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B + eb + 4)
    (fun _ => K) (fun eb hh => (hcallback eb hh).1) (fun eb hh => (hcallback eb hh).2)
  change (arithmeticFlatMapWithWork callback (List.range count)).2 + count + N.bits.length + 2 ≤ _
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hsum count) N.bits.length) 2

end BinaryFraction
end EditApproximation

end OAI
