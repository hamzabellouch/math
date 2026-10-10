import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedCellGroup
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedUnskippedWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryCellCentersWork
import OAI.Combinatorics.EditApproximation.Binary.BinarySelectedGroupWork

namespace OAI

/-! Complete per-cell arithmetic. The count includes construction and
testing of every candidate, and the actual finite-count sampled selector. -/

namespace EditApproximation
namespace BinaryFraction

def preparedCellGroupBitBudget (M T e b P B : ℕ) : ℕ :=
  let V := (40 * P + 2) ^ (2 * M)
  cellCentersBitBudget P P B +
    (P + 1) ^ 2 * (preparedUnskippedBitBudget e b M P V V B + 3) +
    selectedGroupBitBudget M T e b ((P + 1) ^ 2) V B + 2

theorem preparedCellGroupWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F e Q B : ℕ)
    (hbpos : 0 < b) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (raw : List BinaryFraction)
    (hraw : raw.map value = groupDyadicScales M b (nat F).value)
    (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M)
    (hPpos : 0 < P) (cell : ℕ × ℕ)
    (hB : 6 ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hM : Nat.size M + 2 ≤ B)
    (hQ : Nat.size Q + 2 ≤ B) (hb : Nat.size b + 2 ≤ B)
    (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B) (he : e + 1 ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B)
    (hparent : ∀ q, (parentInitial q).width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B)
    (hinitial : ∀ i q, (initial i q).width ≤ B)
    (hcurrent : ∀ i q, (current i q).width ≤ B)
    (hscale : ∀ x ∈ raw, x.width ≤ B)
    (hleft : Nat.size cell.1 ≤ B) (hright : Nat.size cell.2 ≤ B)
    (hbdyadic : ∃ j : ℕ, b = 2 ^ j) (hPdyadic : ∃ j : ℕ, P = 2 ^ j) :
    (preparedCellGroupWithWork source target parent b P F e Q hbpos tau a
      parentInitial child initial current raw hraw draw hPpos cell).2 ≤
      preparedCellGroupBitBudget M (groupDyadicScales M b (nat F).value).length e b P B := by
  let V := (40 * P + 2) ^ (2 * M)
  let centers := cellCentersWithWork P F b a (inversePowerTwo e) parentInitial cell
  let members := filterMapWithWork
    (preparedUnskippedCandidateWithWork source target parent b P e hbpos hPpos tau (nat F) child initial)
    centers.1
  have ht : (inversePowerTwo e).width ≤ B := by rw [inversePowerTwo_width]; exact he
  have htValue : 0 ≤ (inversePowerTwo e).value ∧ (inversePowerTwo e).value ≤ 1 := by
    rw [inversePowerTwo_value, zpow_neg, zpow_natCast]
    exact ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))⟩
  have hc := cellCentersWithWork_uniform_cost P F b B a (inversePowerTwo e) parentInitial cell
    hB (by omega) hb hP hF ha ht hparent hleft hright htValue hbdyadic hPdyadic
  change centers.2 ≤ cellCentersBitBudget P P B at hc
  have hclen : centers.1.length ≤ (P + 1) ^ 2 := by
    rw [cellCentersWithWork_value P F b a (inversePowerTwo e) parentInitial cell hPpos]
    exact cellRepresentativeStates_length_le a.value (fun q => (parentInitial q).value)
      (inversePowerTwo e).value cell htValue hbdyadic hPdyadic
  have hmc := filterMapWithWork_cost
    (preparedUnskippedCandidateWithWork source target parent b P e hbpos hPpos tau (nat F) child initial)
    centers.1 (preparedUnskippedBitBudget e b M P V V B) (fun r _ =>
      preparedUnskippedCandidateWithWork_uniform_cost source target parent b P e B hbpos hPpos
        tau (nat F) child initial r hnx hny (by omega) hb hP he htau
        ((nat_width_le F).trans hF) hchild hinitial)
  change members.2 ≤ _ at hmc
  have hmlen : members.1.length ≤ (P + 1) ^ 2 := by
    have hm : members.1.length ≤ centers.1.length := by
      dsimp only [members]
      rw [filterMapWithWork_value]
      exact List.length_filterMap_le _ _
    exact hm.trans hclen
  have hmc' := hmc.trans (Nat.mul_le_mul_right _ hclen)
  unfold preparedCellGroupWithWork
  dsimp only
  by_cases hempty : members.1 = []
  · rw [dite_eq_left hempty]
    change centers.2 + members.2 + 1 ≤ _
    unfold preparedCellGroupBitBudget
    change _ ≤ cellCentersBitBudget P P B +
      (P + 1) ^ 2 * (preparedUnskippedBitBudget e b M P V V B + 3) + _ + 2
    omega
  · rw [dite_eq_right hempty]
    have hselected := sampledGroupActionWithWork_cost source target parent b P e Q tau (nat F)
      child initial current (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) members.1 hempty V B
      hM hQ hb hny (fun t => hscale _ (List.get_mem _ _))
      (fun member _ => (representativeBandActions_length_le source target parent member.center b P
        tau.value ((2 : ℚ) ^ (-(e : ℤ))) (fun i q => (child i q).value)).trans
          (wideActionList_length_le M parent member.center b P hPpos))
      (fun _ _ _ _ i => hinitial i _) hcurrent
    change (dyadicSampledGroupActionWithWork source target parent b P e Q tau (nat F)
      child initial current raw hraw draw members.1 hempty).2 ≤ _ at hselected
    have hselected' : (dyadicSampledGroupActionWithWork source target parent b P e Q tau (nat F)
        child initial current raw hraw draw members.1 hempty).2 ≤
        selectedGroupBitBudget M (groupDyadicScales M b (nat F).value).length e b ((P + 1) ^ 2) V B := by
      apply hselected.trans
      unfold selectedGroupBitBudget
      gcongr
    change centers.2 + members.2 +
      (dyadicSampledGroupActionWithWork source target parent b P e Q tau (nat F)
        child initial current raw hraw draw members.1 hempty).2 + 2 ≤ _
    unfold preparedCellGroupBitBudget
    change _ ≤ cellCentersBitBudget P P B +
      (P + 1) ^ 2 * (preparedUnskippedBitBudget e b M P V V B + 3) +
      selectedGroupBitBudget M (groupDyadicScales M b (nat F).value).length e b ((P + 1) ^ 2) V B + 2
    omega

end BinaryFraction
end EditApproximation

end OAI
