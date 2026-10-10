import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PartitionLabelCells

namespace OAI

/-! # The three actual balanced-label arrays under the input-scale bound -/

noncomputable section
namespace LowSpaceSubsetSum.PartitionSamplerCells

variable {n : ℕ}

def run (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (s : (PartitionArrayExecution.coupling R z 3 id).Seed) :=
  PartitionLabelCells.family R z 3 id s

theorem value (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (s : (PartitionArrayExecution.coupling R z 3 id).Seed) :
    (run R z s).1 = PartitionArrayExecution.run R z 3 id s :=
  PartitionLabelCells.family_value R z 3 id s

theorem cells (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (hn : 10000 ≤ n) (s : (PartitionArrayExecution.coupling R z 3 id).Seed) :
    (run R z s).2 ≤ inputScale R.input^6 := by
  let u := inputScale R.input
  have hu : n+1 ≤ u := by unfold u inputScale; omega
  have hu0 : 10000 ≤ u := by omega
  have hm : mixerSize n+1 ≤ u := by unfold mixerSize; omega
  have hp3 := Nat.pow_le_pow_left (show n ≤ u by omega) 3
  have hu3 : u ≤ u^3 := by
    simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ u) (by decide : 1 ≤ 3)
  have ht : 3*n^3+160 ≤ 4*u^3 := by nlinarith only [hp3, hu3, hu0]
  have hprod := Nat.mul_le_mul hm ht
  have hprod' : (mixerSize n+1)*(3*n^3+160) ≤ 4*u^4 := by
    convert hprod using 1; ring
  have h16 : 16 ≤ u^4 := by
    have h4 : u ≤ u^4 := by
      simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ u) (by decide : 1 ≤ 4)
    omega
  have h13 : 13*u^4 ≤ u^6 := by
    have h2 : 13 ≤ u^2 := by nlinarith only [hu0]
    calc
      _ ≤ u^2*u^4 := Nat.mul_le_mul_right _ h2
      _ = _ := by rw [← pow_add]
  have h := PartitionLabelCells.family_cells R z 3 id s
  change _ ≤ u^6
  change (run R z s).2 ≤ _ at h
  nlinarith only [h, hprod', h16, h13]

end LowSpaceSubsetSum.PartitionSamplerCells

end

end OAI
