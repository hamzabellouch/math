import OAI.Combinatorics.EditApproximation.Binary.BinaryCellCenters
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGridWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryAffineGuard

namespace OAI

/-! Word-size bounds for the literal whole-cell index scans. The
cardinalities here are the emitted local ranges, not the target length. -/

namespace EditApproximation
namespace BinaryFraction

private theorem naturalWordSize_le (bits : List Bool) : Nat.size (bitWordValue bits) ≤ bits.length :=
  Nat.size_le.mpr (bitWordValue_lt_pow_length bits)

def cellCoordinateSetupBitBudget (B : ℕ) : ℕ :=
  100 * (B + 1) + 4200 * (B + 6) ^ 2 + 400 * (4 * B + 21) ^ 2 + 100 * (4 * B + 25)

theorem cellCoordinatesWithWork_bounds (side : BinaryFraction) (p radius B : ℕ)
    (hs : side.width ≤ B) (hp : Nat.size p ≤ B) (hr : Nat.size radius ≤ B) :
    (cellCoordinatesWithWork side p radius).2 ≤
      cellCoordinateSetupBitBudget B + (localCellCoordinates side.value p radius).length ∧
      ∀ x ∈ (cellCoordinatesWithWork side p radius).1, Nat.size x ≤ 4 * B + 23 := by
  let lower := saturatingSubtractWithWork p radius
  let upper := binaryNaturalAddWithWork p radius
  let firstQ := divWithWork (nat (bitWordValue lower.1)) side
  let lastQ := divWithWork (nat (bitWordValue upper.1)) side
  let first := naturalFloorWithWork firstQ.1
  let last := naturalFloorWithWork lastQ.1
  let stop := binaryNaturalAddWithWork (bitWordValue last.1) 1
  let count := saturatingSubtractWithWork (bitWordValue stop.1) (bitWordValue first.1)
  have hl : Nat.size (bitWordValue lower.1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size (Nat.sub_le _ _)).trans hp
  have hu : Nat.size (bitWordValue upper.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le p radius).trans (by omega)
  have hfl := divWithWork_width_uniform (nat (bitWordValue lower.1)) side (B + 4)
    ((nat_width_le _).trans (by omega)) (by omega)
  have hll := divWithWork_width_uniform (nat (bitWordValue upper.1)) side (B + 4)
    ((nat_width_le _).trans (by omega)) (by omega)
  have hfc := divWithWork_cost (nat (bitWordValue lower.1)) side (B + 4)
    ((nat_width_le _).trans (by omega)) (by omega)
  have hlc := divWithWork_cost (nat (bitWordValue upper.1)) side (B + 4)
    ((nat_width_le _).trans (by omega)) (by omega)
  change firstQ.1.width ≤ _ at hfl
  change lastQ.1.width ≤ _ at hll
  change firstQ.2 ≤ _ at hfc
  change lastQ.2 ≤ _ at hlc
  simp only [Nat.add_assoc, Nat.reduceAdd] at hfc hlc
  have hf := naturalFloorWithWork_bounds firstQ.1
  have hl' := naturalFloorWithWork_bounds lastQ.1
  have hfirst : Nat.size (bitWordValue first.1) ≤ 4 * B + 20 :=
    ((naturalWordSize_le _).trans hf.1).trans (by omega)
  have hlast : Nat.size (bitWordValue last.1) ≤ 4 * B + 20 :=
    ((naturalWordSize_le _).trans hl'.1).trans (by omega)
  have hstop : Nat.size (bitWordValue stop.1) ≤ 4 * B + 23 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le _ 1).trans (by simp only [Nat.size_one]; omega)
  have hfloorFirst : first.2 ≤ 200 * (4 * B + 21) ^ 2 :=
    hf.2.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hfloorLast : last.2 ≤ 200 * (4 * B + 21) ^ 2 :=
    hl'.2.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hlowCost := saturatingSubtractWithWork_cost p radius
  have huppCost := binaryNaturalAddWithWork_cost p radius
  have hstopCost := binaryNaturalAddWithWork_cost (bitWordValue last.1) 1
  have hcountCost := saturatingSubtractWithWork_cost (bitWordValue stop.1) (bitWordValue first.1)
  change lower.2 ≤ _ at hlowCost
  change upper.2 ≤ _ at huppCost
  change stop.2 ≤ _ at hstopCost
  change count.2 ≤ _ at hcountCost
  simp only [Nat.size_one] at hstopCost
  have hlength : (List.range' (bitWordValue first.1) (bitWordValue count.1)).length =
      (localCellCoordinates side.value p radius).length := by
    have hv := congrArg List.length (cellCoordinatesWithWork_value side p radius)
    simpa only [cellCoordinatesWithWork, lower, upper, firstQ, lastQ, first, last,
      stop, count] using hv
  constructor
  · change lower.2 + upper.2 + firstQ.2 + lastQ.2 + first.2 + last.2 + stop.2 + count.2 +
      (List.range' (bitWordValue first.1) (bitWordValue count.1)).length + Nat.size p + Nat.size radius + 9 ≤ _
    rw [hlength]
    unfold cellCoordinateSetupBitBudget
    omega
  · intro x hx
    have hx' : x ∈ List.range' (bitWordValue first.1) (bitWordValue count.1) := by
      simpa only [cellCoordinatesWithWork, lower, upper, firstQ, lastQ, first, last,
        stop, count] using hx
    obtain ⟨j, hj, hxj⟩ := List.mem_range'.mp hx'
    have hcount : bitWordValue count.1 = bitWordValue stop.1 - bitWordValue first.1 :=
      saturatingSubtractWithWork_value _ _
    have hxstop : x ≤ bitWordValue stop.1 := by omega
    exact (Nat.size_le_size hxstop).trans hstop

theorem cellCoordinatesWithWork_cost (side : BinaryFraction) (p radius B : ℕ)
    (hs : side.width ≤ B) (hp : Nat.size p ≤ B) (hr : Nat.size radius ≤ B) :
    (cellCoordinatesWithWork side p radius).2 ≤
      cellCoordinateSetupBitBudget B + (localCellCoordinates side.value p radius).length :=
  (cellCoordinatesWithWork_bounds side p radius B hs hp hr).1

def targetCellsBitBudget (left right B : ℕ) : ℕ :=
  2 * cellCoordinateSetupBitBudget B + left + right + left * (5 * right + 3) + 2

theorem targetCellsWithWork_cost {n : ℕ} (side : BinaryFraction) (radius B : ℕ)
    (query : TargetInterval n) (hs : side.width ≤ B) (hn : Nat.size n ≤ B)
    (hr : Nat.size radius ≤ B) :
    (targetCellsWithWork side radius query).2 ≤ targetCellsBitBudget
      (localCellCoordinates side.value query.lo radius).length
      (localCellCoordinates side.value query.hi radius).length B := by
  let left := cellCoordinatesWithWork side query.lo radius
  let right := cellCoordinatesWithWork side query.hi radius
  have hl := cellCoordinatesWithWork_cost side query.lo radius B hs
    ((Nat.size_le_size (query.ordered.trans query.valid)).trans hn) hr
  have hh := cellCoordinatesWithWork_cost side query.hi radius B hs
    ((Nat.size_le_size query.valid).trans hn) hr
  have hm (lo : ℕ) : (arithmeticMapWithWork (fun hi => ((lo, hi), 1)) right.1).2 ≤
      right.1.length * 4 := arithmeticMapWithWork_cost _ _ 1 (fun _ _ => le_rfl)
  have hf := arithmeticFlatMapWithWork_cost
    (fun lo => arithmeticMapWithWork (fun hi => ((lo, hi), 1)) right.1) left.1
    (right.1.length * 4) right.1.length (fun lo _ => hm lo)
    (fun _ _ => by simp only [arithmeticMapWithWork_value, List.length_map]; exact le_rfl)
  change left.2 ≤ _ at hl
  change right.2 ≤ _ at hh
  change left.2 + right.2 + (arithmeticFlatMapWithWork
    (fun lo => arithmeticMapWithWork (fun hi => ((lo, hi), 1)) right.1) left.1).2 + 2 ≤ _
  have hleft : left.1.length = (localCellCoordinates side.value query.lo radius).length :=
    congrArg List.length (cellCoordinatesWithWork_value side query.lo radius)
  have hright : right.1.length = (localCellCoordinates side.value query.hi radius).length :=
    congrArg List.length (cellCoordinatesWithWork_value side query.hi radius)
  have hflat : (arithmeticFlatMapWithWork
      (fun lo => arithmeticMapWithWork (fun hi => ((lo, hi), 1)) right.1) left.1).2 ≤
      (localCellCoordinates side.value query.lo radius).length *
        (5 * (localCellCoordinates side.value query.hi radius).length + 3) := by
    calc
      _ ≤ left.1.length * (right.1.length * 4 + right.1.length + 3) := hf
      _ = _ := by rw [hleft, hright]; ring
  unfold targetCellsBitBudget
  omega


theorem targetCellsWithWork_keys {n : ℕ} (side : BinaryFraction) (radius B : ℕ)
    (query : TargetInterval n) (hs : side.width ≤ B) (hn : Nat.size n ≤ B)
    (hr : Nat.size radius ≤ B) (cell : ℕ × ℕ)
    (hcell : cell ∈ (targetCellsWithWork side radius query).1) :
    Nat.size cell.1 ≤ 4 * B + 23 ∧ Nat.size cell.2 ≤ 4 * B + 23 := by
  have hl := (cellCoordinatesWithWork_bounds side query.lo radius B hs
    ((Nat.size_le_size (query.ordered.trans query.valid)).trans hn) hr).2
  have hh := (cellCoordinatesWithWork_bounds side query.hi radius B hs
    ((Nat.size_le_size query.valid).trans hn) hr).2
  simp only [targetCellsWithWork, arithmeticFlatMapWithWork_value,
    arithmeticMapWithWork_value] at hcell
  obtain ⟨lo, hlo, hc⟩ := List.mem_flatMap.mp hcell
  obtain ⟨hi, hhi, rfl⟩ := List.mem_map.mp hc
  exact ⟨hl lo hlo, hh hi hhi⟩

def cellGridSetupBitBudget (B : ℕ) : ℕ := 2000000 * (B + 100) ^ 2

def cellGridPointBitBudget (B : ℕ) : ℕ := 1000 * (B + 100) ^ 2

def cellGridPointsBitBudget (count B : ℕ) : ℕ :=
  cellGridSetupBitBudget B + count * (cellGridPointBitBudget B + 5)

theorem cellGridPointsWithWork_bounds (side : BinaryFraction) (g cell B : ℕ)
    (hs : side.width ≤ B) (hg : Nat.size g ≤ B) (hc : Nat.size cell ≤ B) :
    (cellGridPointsWithWork side g cell).2 ≤
      cellGridPointsBitBudget (cellGridPoints side.value g cell).length B ∧
      ∀ x ∈ (cellGridPointsWithWork side g cell).1, Nat.size x ≤ 17 * B + 78 := by
  let next := binaryNaturalAddWithWork cell 1
  let lower := canonicalMulWithWork (nat cell) side
  let upper := canonicalMulWithWork (nat (bitWordValue next.1)) side
  let firstQ := divWithWork lower.1 (nat g)
  let lastQ := divWithWork upper.1 (nat g)
  let first := naturalCeilingWithWork firstQ.1
  let last := naturalCeilingWithWork lastQ.1
  let count := saturatingSubtractWithWork (bitWordValue last.1) (bitWordValue first.1)
  let indices := List.range' (bitWordValue first.1) (bitWordValue count.1)
  have hnext : Nat.size (bitWordValue next.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    have hv := naturalWordSize_le (binaryNaturalAddWithWork cell 1).1
    rw [binaryNaturalAddWithWork_value] at hv
    have hl := bitAddWithWork_length cell.bits (1 : ℕ).bits false
    have h : Nat.size (cell + 1) ≤ max (Nat.size cell) 1 + 1 := by
      simpa only [binaryNaturalAddWithWork, Nat.size_eq_bits_len, Nat.size_one] using hv.trans hl
    omega
  have hlow := canonicalMulWithWork_width (nat cell) side (B + 4)
    ((nat_width_le cell).trans (by omega)) (by omega)
  have hupp := canonicalMulWithWork_width (nat (bitWordValue next.1)) side (B + 4)
    ((nat_width_le _).trans (by omega)) (by omega)
  change lower.1.width ≤ _ at hlow
  change upper.1.width ≤ _ at hupp
  have hfirstQ := divWithWork_width_uniform lower.1 (nat g) (4 * B + 18)
    (by omega) ((nat_width_le g).trans (by omega))
  have hlastQ := divWithWork_width_uniform upper.1 (nat g) (4 * B + 18)
    (by omega) ((nat_width_le g).trans (by omega))
  change firstQ.1.width ≤ _ at hfirstQ
  change lastQ.1.width ≤ _ at hlastQ
  have hfirst : Nat.size (bitWordValue first.1) ≤ 16 * B + 78 := by
    have h := (naturalWordSize_le first.1).trans (naturalCeilingWithWork_length firstQ.1)
    omega
  have hlast : Nat.size (bitWordValue last.1) ≤ 16 * B + 78 := by
    have h := (naturalWordSize_le last.1).trans (naturalCeilingWithWork_length lastQ.1)
    omega
  have hindex (i : ℕ) (hi : i ∈ indices) : Nat.size i ≤ 16 * B + 78 := by
    obtain ⟨j, hj, hij⟩ := List.mem_range'.mp hi
    have hcount : bitWordValue count.1 = bitWordValue last.1 - bitWordValue first.1 :=
      saturatingSubtractWithWork_value _ _
    have hle : i ≤ bitWordValue last.1 := by omega
    exact (Nat.size_le_size hle).trans hlast
  let point := fun i =>
    let product := binaryNaturalMulWithWork g i
    (bitWordValue product.1, product.2 + Nat.size i + 2)
  have hpoint (i : ℕ) (hi : i ∈ indices) : (point i).2 ≤ cellGridPointBitBudget B := by
    have hm := binaryNaturalMulWithWork_cost g i
    have his := hindex i hi
    dsimp only [point]
    unfold cellGridPointBitBudget
    nlinarith only [hm, his, hg, Nat.zero_le B]
  have hmap := arithmeticMapWithWork_cost point indices (cellGridPointBitBudget B) hpoint
  have hmaplen : indices.length = (cellGridPoints side.value g cell).length := by
    have hv := congrArg List.length (cellGridPointsWithWork_value side g cell)
    simpa only [cellGridPointsWithWork, arithmeticMapWithWork_value, List.length_map] using hv
  have hnextc := binaryNaturalAddWithWork_cost cell 1
  have hlowc := canonicalMulWithWork_cost (nat cell) side (B + 4)
    ((nat_width_le cell).trans (by omega)) (by omega)
  have huppc := canonicalMulWithWork_cost (nat (bitWordValue next.1)) side (B + 4)
    ((nat_width_le _).trans (by omega)) (by omega)
  have hfirstc := divWithWork_cost lower.1 (nat g) (4 * B + 18)
    (by omega) ((nat_width_le g).trans (by omega))
  have hlastc := divWithWork_cost upper.1 (nat g) (4 * B + 18)
    (by omega) ((nat_width_le g).trans (by omega))
  have hfc := (naturalCeilingWithWork_cost firstQ.1).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by omega : firstQ.1.width + 1 ≤ 16 * B + 77) 2))
  have hlc := (naturalCeilingWithWork_cost lastQ.1).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by omega : lastQ.1.width + 1 ≤ 16 * B + 77) 2))
  have hcc := saturatingSubtractWithWork_cost (bitWordValue last.1) (bitWordValue first.1)
  change next.2 ≤ _ at hnextc
  change lower.2 ≤ _ at hlowc
  change upper.2 ≤ _ at huppc
  change firstQ.2 ≤ _ at hfirstc
  change lastQ.2 ≤ _ at hlastc
  change first.2 ≤ _ at hfc
  change last.2 ≤ _ at hlc
  change count.2 ≤ _ at hcc
  simp only [Nat.size_one, Nat.add_assoc, Nat.reduceAdd] at hnextc hlowc huppc hfirstc hlastc
  have hsetup : next.2 + lower.2 + upper.2 + firstQ.2 + lastQ.2 + first.2 + last.2 + count.2 +
      Nat.size cell + Nat.size g + 10 ≤ cellGridSetupBitBudget B := by
    unfold cellGridSetupBitBudget
    nlinarith only [hnextc, hlowc, huppc, hfirstc, hlastc, hfc, hlc, hcc,
      hfirst, hlast, hc, hg, Nat.zero_le B]
  constructor
  · change next.2 + lower.2 + upper.2 + firstQ.2 + lastQ.2 + first.2 + last.2 + count.2 +
      (arithmeticMapWithWork point indices).2 + indices.length + Nat.size cell + Nat.size g + 10 ≤ _
    unfold cellGridPointsBitBudget
    rw [← hmaplen]
    nlinarith only [hsetup, hmap, Nat.zero_le indices.length]
  · intro x hx
    have hx' : x ∈ (arithmeticMapWithWork point indices).1 := by
      simpa only [cellGridPointsWithWork, next, lower, upper, firstQ, lastQ, first,
        last, count, indices, point] using hx
    rw [arithmeticMapWithWork_value] at hx'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    dsimp only [point]
    rw [binaryNaturalMulWithWork_value]
    have hprod := natural_product_bit_length g i
    have hidx := hindex i hi
    omega

theorem cellGridPointsWithWork_cost (side : BinaryFraction) (g cell B : ℕ)
    (hs : side.width ≤ B) (hg : Nat.size g ≤ B) (hc : Nat.size cell ≤ B) :
    (cellGridPointsWithWork side g cell).2 ≤
      cellGridPointsBitBudget (cellGridPoints side.value g cell).length B :=
  (cellGridPointsWithWork_bounds side g cell B hs hg hc).1


def cellStatesBitBudget (left right B : ℕ) : ℕ :=
  cellGridPointsBitBudget left B + cellGridPointsBitBudget right B +
    left * (right * (16 * (17 * B + 78) + 11) + right + 3) + 2

theorem cellStatesWithWork_cost (n g B : ℕ) (side : BinaryFraction) (cell : ℕ × ℕ)
    (hn : Nat.size n ≤ B) (hg : Nat.size g ≤ B) (hs : side.width ≤ B)
    (hleft : Nat.size cell.1 ≤ B) (hright : Nat.size cell.2 ≤ B) :
    (cellStatesWithWork n g side cell).2 ≤ cellStatesBitBudget
      (cellGridPoints side.value g cell.1).length (cellGridPoints side.value g cell.2).length B := by
  let left := cellGridPointsWithWork side g cell.1
  let right := cellGridPointsWithWork side g cell.2
  have hl := cellGridPointsWithWork_bounds side g cell.1 B hs hg hleft
  have hr := cellGridPointsWithWork_bounds side g cell.2 B hs hg hright
  have htest (lo : ℕ) (hlo : lo ∈ left.1) :
      (filterMapWithWork (makeStateWithWork n lo) right.1).2 ≤
        right.1.length * (16 * (17 * B + 78) + 11) := by
    exact filterMapWithWork_cost _ _ (16 * (17 * B + 78) + 8) (fun hi hhi =>
      makeStateWithWork_cost n lo hi (17 * B + 78) (by omega) (hl.2 lo hlo) (hr.2 hi hhi))
  have hlen (lo : ℕ) : (filterMapWithWork (makeStateWithWork n lo) right.1).1.length ≤
      right.1.length := by
    rw [filterMapWithWork_value]
    exact List.length_filterMap_le _ _
  have hf := arithmeticFlatMapWithWork_cost (fun lo => filterMapWithWork (makeStateWithWork n lo) right.1)
    left.1 (right.1.length * (16 * (17 * B + 78) + 11)) right.1.length
    htest (fun lo _ => hlen lo)
  have hll : left.1.length = (cellGridPoints side.value g cell.1).length :=
    congrArg List.length (cellGridPointsWithWork_value side g cell.1)
  have hrl : right.1.length = (cellGridPoints side.value g cell.2).length :=
    congrArg List.length (cellGridPointsWithWork_value side g cell.2)
  rw [hll, hrl] at hf
  change left.2 + right.2 + (arithmeticFlatMapWithWork
    (fun lo => filterMapWithWork (makeStateWithWork n lo) right.1) left.1).2 + 2 ≤ _
  unfold cellStatesBitBudget
  have hlc : left.2 ≤ _ := hl.1
  have hrc : right.2 ≤ _ := hr.1
  omega

end BinaryFraction
end EditApproximation

end OAI
