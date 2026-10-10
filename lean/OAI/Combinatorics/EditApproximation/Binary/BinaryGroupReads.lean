import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundedReads
import OAI.Combinatorics.EditApproximation.Binary.BinarySampledGroups

namespace OAI

/-! Group estimates and the ordered minimizing scan retain finite-table
lookup costs, using Fin-indexed source arrays. -/

namespace EditApproximation
namespace BinaryFraction

theorem scoredArgmaxWithWork_extra {α : Type*} (read plain : α → BinaryFraction × ℕ)
    (extra : α → ℕ) (xs : List α)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 + extra x) :
    (scoredArgmaxWithWork read xs).1 = (scoredArgmaxWithWork plain xs).1 ∧
    (scoredArgmaxWithWork read xs).2 ≤
      (scoredArgmaxWithWork plain xs).2 + (xs.map extra).sum := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [scoredArgmaxWithWork, List.map_nil, List.sum_nil,
      Nat.add_zero, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    simp only [scoredArgmaxWithWork, ht.1, hx, List.map_cons, List.sum_cons]
    cases (scoredArgmaxWithWork plain xs).1 with
    | none => exact ⟨rfl, by dsimp only; omega⟩
    | some best => exact ⟨rfl, by dsimp only; omega⟩

theorem selectGroupWithWork_extra {α : Type*} (read plain : α → BinaryFraction × ℕ)
    (extra : α → ℕ) (xs : List α) (hne : xs ≠ [])
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 + extra x) :
    (selectGroupWithWork xs hne read).1 = (selectGroupWithWork xs hne plain).1 ∧
    (selectGroupWithWork xs hne read).2 ≤
      (selectGroupWithWork xs hne plain).2 + (xs.map extra).sum := by
  have h := scoredArgmaxWithWork_extra
    (fun x => ((read x).1.neg, (read x).2 + 1))
    (fun x => ((plain x).1.neg, (plain x).2 + 1)) extra xs
    (fun x hx => by rw [hv x hx]) (fun x hx => by have := hc x hx; omega)
  unfold selectGroupWithWork
  dsimp only
  rw [h.1]
  exact ⟨rfl, by omega⟩

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q))
  (fun i q => BinaryFraction.value (Prod.fst (initial i q)))

def unskippedEstimateReadWithWork (member : Member) : BinaryFraction × ℕ :=
  let mass := envelopeVectorReadWithWork b member.actions initial
  let rounded := roundedBandReadWithWork exponent b member.actions member.nonempty initial
  let values := vectorMapWithWork M fun i => current i (rounded.1.get i)
  let connection := endpointConnectionWithWork member.center rounded.1.get
  let result := countedGroupMemberWithWork Q b scales connection.1 mass.1 values.1 draw
  (result.1, mass.2 + rounded.2 + values.2 + connection.2 + result.2 + 5)

theorem unskippedEstimateReadWithWork_eq_cost (member : Member) (R C : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ C) (hr : ∀ i q, (current i q).2 ≤ R) :
    (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).1 =
      (unskippedEstimateWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw member).1 ∧
    (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).2 ≤
      (unskippedEstimateWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw member).2 +
      M * (member.actions.length * (C + 3)) + M * (member.actions.length * (C + 3)) + M * R := by
  have hm := envelopeVectorReadWithWork_eq_cost b member.actions initial C hi
  have hp := roundedBandReadWithWork_eq_cost exponent b member.actions member.nonempty initial C hi
  have hv := vectorMapWithWork_extra M
    (fun i => current i ((roundedBandWithWork exponent b member.actions member.nonempty
      (fun j q => (initial j q).1)).1.get i))
    (fun i => ((current i ((roundedBandWithWork exponent b member.actions member.nonempty
      (fun j q => (initial j q).1)).1.get i)).1, 1)) R (fun _ => rfl)
    (fun i => by have := hr i ((roundedBandWithWork exponent b member.actions member.nonempty
      (fun j q => (initial j q).1)).1.get i); omega)
  unfold unskippedEstimateReadWithWork unskippedEstimateWithWork
  dsimp only
  rw [hm.1, hp.1, hv.1]
  exact ⟨rfl, by omega⟩

def chooseUnskippedReadWithWork (members : List Member) (hne : members ≠ []) : Member × ℕ :=
  selectGroupWithWork members hne
    (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current scales draw)

theorem chooseUnskippedReadWithWork_eq_cost (members : List Member) (hne : members ≠ []) (R C : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ C) (hr : ∀ i q, (current i q).2 ≤ R) :
    (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1 ∧
    (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤
      (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).2 +
      (members.map fun member => M * (member.actions.length * (C + 3)) +
        M * (member.actions.length * (C + 3)) + M * R).sum := by
  exact selectGroupWithWork_extra _ _ _ members hne
    (fun member _ => (unskippedEstimateReadWithWork_eq_cost source target parent b P exponent Q
      tau F child initial current scales draw member R C hi hr).1)
    (fun member _ => by
      simpa only [Nat.add_assoc] using
        (unskippedEstimateReadWithWork_eq_cost source target parent b P exponent Q
          tau F child initial current scales draw member R C hi hr).2)

end Group
end BinaryFraction
end EditApproximation

end OAI
