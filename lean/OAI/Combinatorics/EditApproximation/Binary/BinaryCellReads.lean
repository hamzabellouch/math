import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupActionReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryUnskippedReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedCellGroup
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Reader-aware whole-cell construction. Every eligibility test reads its
initial word, and every accepted band and selected action uses the counted
reader kernels. -/

namespace EditApproximation

theorem filterMapWithWork_extra {α β : Type*} (read plain : α → Option β × ℕ)
    (extra : α → ℕ) (xs : List α)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 + extra x) :
    (filterMapWithWork read xs).1 = (filterMapWithWork plain xs).1 ∧
    (filterMapWithWork read xs).2 ≤ (filterMapWithWork plain xs).2 + (xs.map extra).sum := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [filterMapWithWork, List.map_nil, List.sum_nil,
      Nat.add_zero, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    simp only [filterMapWithWork, hx, ht.1, List.map_cons, List.sum_cons]
    cases (plain x).1 with
    | none => exact ⟨trivial, by omega⟩
    | some value => exact ⟨trivial, by omega⟩

namespace BinaryFraction



theorem cellCentersReadWithWork_eq_cost {n : ℕ} (P F b : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction × ℕ) (cell : ℕ × ℕ)
    (R : ℕ) (hr : ∀ r, (initial r).2 ≤ R) :
    (cellCentersReadWithWork P F b a theta initial cell).1 =
      (cellCentersWithWork P F b a theta (fun r => (initial r).1) cell).1 ∧
    (cellCentersReadWithWork P F b a theta initial cell).2 ≤
      (cellCentersWithWork P F b a theta (fun r => (initial r).1) cell).2 * (R + 1) := by
  have hs := filterWithWork_add_read
    (fun r => centerEligibilityWithWork b F a (initial r).1) (fun r => (initial r).2)
    (cellStatesWithWork n (bitWordValue (seedGridSpacingWithWork b P).1)
      (canonicalMulWithWork theta (nat b)).1 cell).1 R (fun r _ => hr r)
  unfold cellCentersReadWithWork cellCentersWithWork
  dsimp only
  have he : (fun r => let word := initial r; let tested := centerEligibilityWithWork b F a word.1;
      (tested.1, word.2 + tested.2)) =
      (fun r => ((centerEligibilityWithWork b F a (initial r).1).1,
        (centerEligibilityWithWork b F a (initial r).1).2 + (initial r).2)) := by
    funext r
    simp only [Nat.add_comm]
  rw [he, hs.1]
  exact ⟨rfl, by nlinarith only [hs.2]⟩

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R C : ℕ) (hr : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M)

def preparedCellGroupReadWithWork (cell : ℕ × ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let centers := cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell
  let members := filterMapWithWork
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R C hr hi) centers.1
  if h : members.1 = [] then (none, centers.2 + members.2 + 1) else
    let selected := dyadicSampledGroupActionReadWithWork source target parent b P exponent Q tau (nat F)
      (fun i q => (child i q).1) initial current raw hraw draw members.1 h
    (some selected.1, centers.2 + members.2 + selected.2 + 2)

theorem preparedCellGroupReadWithWork_eq (cell : ℕ × ℕ) (Rp Rc : ℕ)
    (hp : ∀ r, (parentInitial r).2 ≤ Rp) (hc : ∀ i q, (current i q).2 ≤ Rc) :
    (preparedCellGroupReadWithWork source target parent b P F exponent Q hb hP tau a
      parentInitial child initial current R C hr hi raw hraw draw cell).1 =
    (preparedCellGroupWithWork source target parent b P F exponent Q hb tau a
      (fun r => (parentInitial r).1) (fun i q => (child i q).1)
      (fun i q => (initial i q).1) (fun i q => (current i q).1) raw hraw draw hP cell).1 := by
  have hcenters := (cellCentersReadWithWork_eq_cost P F b a (inversePowerTwo exponent)
    parentInitial cell Rp hp).1
  have hm : (filterMapWithWork
      (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
        child initial R C hr hi)
      (cellCentersWithWork P F b a (inversePowerTwo exponent) (fun r => (parentInitial r).1) cell).1).1 =
    (filterMapWithWork
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
        (fun i q => (child i q).1) (fun i q => (initial i q).1))
      (cellCentersWithWork P F b a (inversePowerTwo exponent) (fun r => (parentInitial r).1) cell).1).1 := by
    simp only [filterMapWithWork_value, preparedUnskippedReadWithWork_value]
  unfold preparedCellGroupReadWithWork preparedCellGroupWithWork
  dsimp only
  simp only [hcenters, hm]
  split_ifs with hempty
  · rfl
  · apply congrArg some
    exact (sampledGroupActionReadWithWork_eq_cost source target parent b P exponent Q tau (nat F)
      (fun i q => (child i q).1) initial current _ _ _ hempty Rc C hi hc).1

end Cell
end BinaryFraction
end EditApproximation

end OAI
