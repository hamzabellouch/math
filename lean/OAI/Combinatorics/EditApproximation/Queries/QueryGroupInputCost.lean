import OAI.Combinatorics.EditApproximation.Queries.QueryGroupLabelCost
import OAI.Combinatorics.EditApproximation.Queries.QueryRoundedStateCost
import OAI.Combinatorics.EditApproximation.Queries.QueryRoundedCounts

namespace OAI

namespace EditApproximation.BinaryFraction

def queryGroupInputsLength (M exponent : ℕ) : ℕ :=
  M * ((24 * 2 ^ exponent * M + 2) * (4 * 2 ^ exponent + 4))

def queryGroupInputsBitBudget (M exponent B R : ℕ) : ℕ :=
  let L := (24 * 2 ^ exponent * M + 2) * (4 * 2 ^ exponent + 4)
  queryGroupLabelsBitBudget M B R +
    M * (queryRoundedStatesBitBudget (24 * 2 ^ exponent * M + 2) (4 * 2 ^ exponent + 4) exponent B +
      5 * L + 4) + 1

theorem queryGroupInputsWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (b exponent Q B R : ℕ) (cell : ℕ × ℕ) (h : BinaryFraction)
    (draw : Fin (groupSampleCount M Q b h.value) → Fin M × ℕ)
    (hB : 4 ≤ B) (hMpos : 0 < M) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B) (hb : Nat.size b + 2 ≤ B)
    (hc : Nat.size cell.1 ≤ B) (he : exponent + 1 ≤ B) (hh : h.width ≤ B)
    (hhv : 0 ≤ h.value) (hfloor : (b : ℚ) / M ≤ h.value) (hR : ∀ i, (draw i).2 ≤ R) :
    (queryGroupInputsWithWork (ny := ny) parent b exponent Q cell h draw).1.length ≤
      queryGroupInputsLength M exponent ∧
    (queryGroupInputsWithWork (ny := ny) parent b exponent Q cell h draw).2 ≤
      queryGroupInputsBitBudget M exponent B R := by
  let labels := queryGroupLabelsWithWork M Q b h draw
  let L := (24 * 2 ^ exponent * M + 2) * (4 * 2 ^ exponent + 4)
  let C := queryRoundedStatesBitBudget (24 * 2 ^ exponent * M + 2) (4 * 2 ^ exponent + 4) exponent B
  let run := fun i : Fin M =>
    let states := queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h
    let tagged := arithmeticMapWithWork (fun r => ((i, r), 1)) states.1
    (tagged.1, states.2 + tagged.2 + 1)
  have hl := queryGroupLabelsWithWork_bounds M Q b B R h draw hM hQ hb hh hR
  have hcounts := groupRoundSpacing_endpoint_counts M b exponent h.value hMpos hhv hfloor
  have hs (i : Fin M) := queryGroupRoundedStatesWithWork_bounds (ny := ny) parent b exponent B
    (24 * 2 ^ exponent * M + 2) (4 * 2 ^ exponent + 4) cell i h hB hnx hny (by omega)
    (by omega) hc he hh hcounts.1 hcounts.2
  have hrun (i : Fin M) : (run i).1.length ≤ L ∧ (run i).2 ≤ C + 4 * L + 1 := by
    have hm := (arithmeticMapWithWork_cost (fun r => ((i, r), 1))
      (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).1 1
      (fun _ _ => le_rfl)).trans (Nat.mul_le_mul_right _ (hs i).1)
    constructor
    · simpa only [run, arithmeticMapWithWork_value, List.length_map] using (hs i).1
    · change (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).2 +
        (arithmeticMapWithWork (fun r => ((i, r), 1))
          (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).1).2 + 1 ≤ _
      have hsc : (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).2 ≤ C := (hs i).2
      change _ ≤ L * 4 at hm
      rw [Nat.mul_comm L 4] at hm
      omega
  have hlen := (arithmeticFlatMapWithWork_length run labels.1 L
    (fun i _ => (hrun i).1)).trans (Nat.mul_le_mul_right _ hl.1)
  have hcost := (arithmeticFlatMapWithWork_cost run labels.1 (C + 4 * L + 1) L
    (fun i _ => (hrun i).2) (fun i _ => (hrun i).1)).trans (Nat.mul_le_mul_right _ hl.1)
  rw [show C + 4 * L + 1 + L + 3 = C + 5 * L + 4 by omega] at hcost
  have hinputCost : labels.2 + (arithmeticFlatMapWithWork run labels.1).2 + 1 ≤
      queryGroupInputsBitBudget M exponent B R := by
    have hlc : labels.2 ≤ queryGroupLabelsBitBudget M B R := hl.2
    simpa only [queryGroupInputsBitBudget, C, L] using
      Nat.add_le_add_right (Nat.add_le_add hlc hcost) 1
  simpa only [queryGroupInputsWithWork, labels, run, queryGroupInputsLength, L] using
    And.intro hlen hinputCost

end EditApproximation.BinaryFraction

end OAI
