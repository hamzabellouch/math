import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyEncoding
import OAI.Combinatorics.EditApproximation.Refinement.ComputedSourceAddressBits
import OAI.Combinatorics.EditApproximation.Refinement.ComputedWarmupReadBudget
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRequestBits

namespace OAI

namespace EditApproximation

 theorem computed_physicalScalarCode_bound (N nx ny R : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
    (hR : R ≤ inputHeight N ^ 2)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (key : PhysicalScalarKey (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) N ny (40 * smallLogExponent N)
      (inputSmallLog N) (inputSmallLog N ^ 80) R
      (localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N))) :
    physicalScalarCode key < 2 ^ (64 * (64 * inputHeight N) + 1) := by
  let H := inputHeight N
  let M := (integerParameters N).M
  let J := intervalTreeDepth M nx
  have hMH : M ≤ H := Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
  have hMpos : 1 ≤ M := (by omega : 1 ≤ 2).trans (computed_branching_bounds N hN hell).1
  have hH : 64 ≤ H := (by omega : 64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hlift (e : ℕ) (he : e ≤ 64 * H) : 2 ^ e ≤ 2 ^ (64 * H) :=
    Nat.pow_le_pow_right (by decide) he
  have hHpow : H ^ 2 ≤ 2 ^ (2 * H) := by
    calc
      _ ≤ (2 ^ H) ^ 2 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hentry : ∀ entry : PhysicalEntry M J ny, physicalEntryCode entry < 2 ^ (64 * H) := by
    intro entry
    exact ((physicalEntryCode_bound hMpos entry).trans_le
      (computed_entryCapacity_bound N nx ny hN hell hnx hny)).trans_le (hlift (5 * H) (by omega))
  have hnode : ∀ node : PhysicalNode M J, physicalNodeCode node < 2 ^ (64 * H) := by
    intro node
    have hb : M ^ J * (J + 1) ≤ 2 ^ (5 * H) := by
      simpa only [PhysicalTableRequest.entryCapacity, zero_add, one_pow, one_mul] using
        computed_entryCapacity_bound N nx 0 hN hell hnx (Nat.zero_le N)
    exact ((physicalNodeCode_bound hMpos node).trans_le hb).trans_le (hlift (5 * H) (by omega))
  have hsmall : smallLogExponent N ≤ H :=
    (Nat.lt_two_pow_self.le : smallLogExponent N ≤ 2 ^ smallLogExponent N).trans
      (computed_smallLog_le_height N)
  have hcell : ny * 2 ^ (40 * smallLogExponent N) + 1 ≤ 2 ^ (64 * H) := by
    have hn : ny ≤ 2 ^ H := hny.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
    have he : 2 ^ (40 * smallLogExponent N) ≤ 2 ^ (40 * H) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 40 hsmall)
    calc
      _ ≤ 2 ^ H * 2 ^ (40 * H) + 1 := Nat.add_le_add_right (Nat.mul_le_mul hn he) 1
      _ = 2 ^ (41 * H) + 1 := by rw [← pow_add]; congr 2; omega
      _ ≤ 2 ^ (41 * H) + 2 ^ (41 * H) := Nat.add_le_add_left Nat.one_le_two_pow _
      _ = 2 ^ (41 * H + 1) := by rw [pow_succ]; omega
      _ ≤ _ := hlift _ (by omega)
  apply physicalScalarCode_bound (64 * H) hnode hentry
  · exact (computed_dyadicScales_length N (by omega)).trans (hHpow.trans (hlift _ (by omega)))
  · exact hcell
  · have hb := Nat.lt_size_self (localOnlineMassBound M (integerParameters N).P H)
    exact (Nat.succ_le_of_lt hb).trans
      ((Nat.pow_le_pow_right (by decide) hB).trans (hlift H (by omega)))
  · exact hR.trans (hHpow.trans (hlift _ (by omega)))
  · exact hMH.trans (Nat.lt_two_pow_self.le.trans (hlift H (by omega)))
  · intro scale
    have hs := List.get_mem (dyadicScales N) scale
    obtain ⟨eb, _, heq⟩ := List.mem_map.mp hs
    have hc : (groupDyadicScales M ((dyadicScales N).get scale) (inputSmallLog N)).length ≤
        2 * inputSmallLog N := by
      rw [← heq]
      exact computed_group_scale_count N eb hN (by omega)
    have htwo : 2 * inputSmallLog N ≤ 2 ^ (H + 1) := by
      have hp := Nat.mul_le_mul_left 2 ((computed_smallLog_le_height N).trans Nat.lt_two_pow_self.le)
      simpa only [pow_succ, Nat.mul_comm] using hp
    exact hc.trans (htwo.trans (hlift _ (by omega)))

end EditApproximation

end OAI
