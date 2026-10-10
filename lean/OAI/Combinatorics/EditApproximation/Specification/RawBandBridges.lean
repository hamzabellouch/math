import OAI.Combinatorics.EditApproximation.Specification.RawBandConsumers
import OAI.Combinatorics.EditApproximation.Definitions

namespace OAI.EditApproximation

theorem filterMapWithWork_map_raw {α β γ : Type*} (f : α → Option β × ℕ)
    (g : β → γ) (xs : List α) :
    filterMapWithWork (fun x => Prod.map (Option.map g) id (f x)) xs =
      Prod.map (List.map g) id (filterMapWithWork f xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Prod.map, id_eq] at ih
    simp only [filterMapWithWork, Prod.map, id_eq, ih]
    cases (f x).1 <;> rfl

theorem filterMapAllocation_map_raw {α β γ : Type*} (f : α → Option β × ℕ)
    (g : β → γ) (allocation : α → ℕ) (xs : List α) :
    filterMapAllocation (fun x => Prod.map (Option.map g) id (f x)) allocation xs =
      filterMapAllocation f allocation xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Prod.map] at ih
    simp only [filterMapAllocation, Prod.map, ih, Option.isSome_map]

namespace BinaryFraction

theorem scoredArgmaxWithWork_map_raw {α β : Type*} (mapping : α → β)
    (score : β → BinaryFraction × ℕ) (values : List α) :
    scoredArgmaxWithWork score (values.map mapping) =
      Prod.map (Option.map (fun result => (mapping result.1, result.2))) id
        (scoredArgmaxWithWork (fun a => score (mapping a)) values) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, scoredArgmaxWithWork, ih, Prod.map, id_eq]
    cases (scoredArgmaxWithWork (fun a => score (mapping a)) tail).1 with
    | none => rfl
    | some best =>
      simp only [Option.map_some]
      split_ifs <;> rfl

theorem selectGroupWithWork_map_raw {α β : Type*} (mapping : α → β)
    (score : β → BinaryFraction × ℕ) (values : List α) (hne : values ≠ []) :
    selectGroupWithWork (values.map mapping) (by simpa using hne) score =
      Prod.map mapping id (selectGroupWithWork values hne (fun a => score (mapping a))) := by
  unfold selectGroupWithWork
  rw [scoredArgmaxWithWork_map_raw]
  simp only [Prod.map, id_eq, Option.map_map, Function.comp_def]
  cases values with
  | nil => exact False.elim (hne rfl)
  | cons head tail =>
    simp only [List.map_cons, List.head_cons]
    cases (scoredArgmaxWithWork (fun a => ((score (mapping a)).1.neg, (score (mapping a)).2 + 1))
      (head :: tail)).1 <;> rfl

theorem scoredArgmaxAllocation_map_raw {α β : Type*} (mapping : α → β)
    (score : β → BinaryFraction × ℕ) (allocation : β → ℕ) (values : List α) :
    scoredArgmaxAllocation score allocation (values.map mapping) =
      scoredArgmaxAllocation (fun a => score (mapping a)) (fun a => allocation (mapping a)) values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, scoredArgmaxAllocation, ih, scoredArgmaxWithWork_map_raw, Prod.map]
    cases (scoredArgmaxWithWork (fun a => score (mapping a)) tail).1 <;> rfl

theorem selectGroupAllocation_map_raw {α β : Type*} (mapping : α → β)
    (score : β → BinaryFraction × ℕ) (allocation : β → ℕ) (values : List α) :
    selectGroupAllocation (values.map mapping) score allocation =
      selectGroupAllocation values (fun a => score (mapping a)) (fun a => allocation (mapping a)) := by
  exact scoredArgmaxAllocation_map_raw mapping _ allocation values

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction) (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)
  (drawSource : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)
  (drawAllocation : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → ℕ)

local notation "Member" => UnskippedBand source target parent b P exponent (value tau) (value F)
  (fun i q => value (child i q)) (fun i q => value (Prod.fst (initial i q)))

theorem unskippedEstimateReadWithWorkRaw_eq (member : Member) :
    unskippedEstimateReadWithWorkRaw b exponent Q initial current scales draw member.raw =
      unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
        scales draw member := rfl

theorem unskippedEstimateSourceWithWorkRaw_eq (member : Member) :
    unskippedEstimateSourceWithWorkRaw b exponent Q initial current scales drawSource member.raw =
      unskippedEstimateSourceWithWork source target parent b P exponent Q tau F child initial current
        scales drawSource member := rfl

theorem chooseUnskippedReadWithWorkRaw_eq (members : List Member) (hne : members ≠ []) :
    chooseUnskippedReadWithWorkRaw b exponent Q initial current scales draw
      (members.map UnskippedBand.raw) (by simpa using hne) =
      Prod.map UnskippedBand.raw id
        (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
          scales draw members hne) := by
  exact selectGroupWithWork_map_raw UnskippedBand.raw _ members hne

theorem chooseUnskippedSourceWithWorkRaw_eq (members : List Member) (hne : members ≠ []) :
    chooseUnskippedSourceWithWorkRaw b exponent Q initial current scales drawSource
      (members.map UnskippedBand.raw) (by simpa using hne) =
      Prod.map UnskippedBand.raw id
        (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current
          scales drawSource members hne) := by
  exact selectGroupWithWork_map_raw UnskippedBand.raw _ members hne

theorem sampledGroupActionReadWithWorkRaw_eq (members : List Member) (hne : members ≠ []) :
    sampledGroupActionReadWithWorkRaw b exponent Q initial current scales draw
      (members.map UnskippedBand.raw) (by simpa using hne) =
      sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
        scales draw members hne := by
  let finish := fun selected : RawUnskippedBand M target.length × ℕ =>
    let rounded := roundedBandReadWithWork exponent b selected.1.actions selected.1.nonempty initial
    let result := endpointActionWithWork selected.1.center rounded.1.get
    (result.1, selected.2 + rounded.2 + result.2 + 3)
  exact congrArg finish (chooseUnskippedReadWithWorkRaw_eq source target parent b P exponent Q
    tau F child initial current scales draw members hne)

theorem sampledGroupActionSourceWithWorkRaw_eq (members : List Member) (hne : members ≠ []) :
    sampledGroupActionSourceWithWorkRaw b exponent Q initial current scales drawSource
      (members.map UnskippedBand.raw) (by simpa using hne) =
      sampledGroupActionSourceWithWork source target parent b P exponent Q tau F child initial current
        scales drawSource members hne := by
  let finish := fun selected : RawUnskippedBand M target.length × ℕ =>
    let rounded := roundedBandReadWithWork exponent b selected.1.actions selected.1.nonempty initial
    let result := endpointActionWithWork selected.1.center rounded.1.get
    (result.1, selected.2 + rounded.2 + result.2 + 3)
  exact congrArg finish (chooseUnskippedSourceWithWorkRaw_eq source target parent b P exponent Q
    tau F child initial current scales drawSource members hne)

theorem unskippedEstimateSourceAllocationRaw_eq (member : Member) :
    unskippedEstimateSourceAllocationRaw b exponent Q initial current initialAllocation currentAllocation
      scales drawSource drawAllocation member.raw =
      unskippedEstimateSourceAllocation source target parent b P exponent Q tau F child initial current
        initialAllocation currentAllocation scales drawSource drawAllocation member := rfl

theorem chooseUnskippedSourceAllocationRaw_eq (members : List Member) :
    chooseUnskippedSourceAllocationRaw b exponent Q initial current initialAllocation currentAllocation
      scales drawSource drawAllocation (members.map UnskippedBand.raw) =
      chooseUnskippedSourceAllocation source target parent b P exponent Q tau F child initial current
        initialAllocation currentAllocation scales drawSource drawAllocation members := by
  exact selectGroupAllocation_map_raw UnskippedBand.raw _ _ members

theorem sampledGroupActionSourceAllocationRaw_eq (members : List Member) (hne : members ≠ []) :
    sampledGroupActionSourceAllocationRaw b exponent Q initial current initialAllocation currentAllocation
      scales drawSource drawAllocation (members.map UnskippedBand.raw) (by simpa using hne) =
      sampledGroupActionSourceAllocation source target parent b P exponent Q tau F child initial current
        initialAllocation currentAllocation scales drawSource drawAllocation members hne := by
  unfold sampledGroupActionSourceAllocationRaw sampledGroupActionSourceAllocation
  rw [chooseUnskippedSourceWithWorkRaw_eq, chooseUnskippedSourceAllocationRaw_eq]
  rfl

end Group
end BinaryFraction
end OAI.EditApproximation
