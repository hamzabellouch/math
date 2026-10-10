import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupMemberSource
import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupReadCosts

namespace OAI

/-! Table-reader and random-source costs are retained together through
member estimation, tie-broken selection, and rounded action return. -/

namespace EditApproximation.BinaryFraction

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)

local notation "Member" => UnskippedBand source target parent b P exponent (value tau) (value F)
  (fun i q => value (child i q)) (fun i q => value (Prod.fst (initial i q)))

def unskippedEstimateSourceWithWork (member : Member) : BinaryFraction × ℕ :=
  let mass := envelopeVectorReadWithWork b member.actions initial
  let rounded := roundedBandReadWithWork exponent b member.actions member.nonempty initial
  let values := vectorMapWithWork M fun i => current i (rounded.1.get i)
  let connection := endpointConnectionWithWork member.center rounded.1.get
  let result := countedGroupMemberSourceWithWork Q b scales connection.1 mass.1 values.1 draw
  (result.1, mass.2 + rounded.2 + values.2 + connection.2 + result.2 + 5)

theorem unskippedEstimateSourceWithWork_eq_cost (member : Member) (R : ℕ)
    (hr : ∀ s i, (draw s i).2 ≤ R) :
    (unskippedEstimateSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).1 =
      (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) member).1 ∧
    (unskippedEstimateSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).2 ≤
      (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) member).2 * (R + 4) := by
  have h := countedGroupMemberSourceWithWork_eq_cost Q b scales
    (endpointConnectionWithWork member.center
      (roundedBandReadWithWork exponent b member.actions member.nonempty initial).1.get).1
    (envelopeVectorReadWithWork b member.actions initial).1
    (vectorMapWithWork M fun i => current i
      ((roundedBandReadWithWork exponent b member.actions member.nonempty initial).1.get i)).1 draw R hr
  unfold unskippedEstimateSourceWithWork unskippedEstimateReadWithWork
  dsimp only
  rw [h.1]
  exact ⟨rfl, by nlinarith only [h.2]⟩

theorem unskippedEstimateSourceWithWork_value (member : Member) :
    (unskippedEstimateSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).1 =
      (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) member).1 := by
  exact countedGroupMemberSourceWithWork_value Q b scales _ _ _ draw

def chooseUnskippedSourceWithWork (members : List Member) (hne : members ≠ []) : Member × ℕ :=
  selectGroupWithWork members hne
    (unskippedEstimateSourceWithWork source target parent b P exponent Q tau F child initial current scales draw)

theorem chooseUnskippedSourceWithWork_eq_cost (members : List Member) (hne : members ≠ [])
    (R : ℕ) (hr : ∀ s i, (draw s i).2 ≤ R) :
    (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) members hne).1 ∧
    (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤
      (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) members hne).2 * (R + 4) := by
  exact selectGroupWithWork_factor _ _ members hne (R + 4) (by omega)
    (fun member _ => (unskippedEstimateSourceWithWork_eq_cost source target parent b P exponent Q
      tau F child initial current scales draw member R hr).1)
    (fun member _ => (unskippedEstimateSourceWithWork_eq_cost source target parent b P exponent Q
      tau F child initial current scales draw member R hr).2)

theorem chooseUnskippedSourceWithWork_value (members : List Member) (hne : members ≠ []) :
    (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) members hne).1 := by
  simp only [chooseUnskippedSourceWithWork, chooseUnskippedReadWithWork, selectGroupWithWork_value]
  congr 1
  funext member
  rw [unskippedEstimateSourceWithWork_value]

def sampledGroupActionSourceWithWork (members : List Member) (hne : members ≠ []) :
    BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M × ℕ :=
  let selected := chooseUnskippedSourceWithWork source target parent b P exponent Q tau F
    child initial current scales draw members hne
  let rounded := roundedBandReadWithWork exponent b selected.1.actions selected.1.nonempty initial
  let result := endpointActionWithWork selected.1.center rounded.1.get
  (result.1, selected.2 + rounded.2 + result.2 + 3)

theorem sampledGroupActionSourceWithWork_eq_cost (members : List Member) (hne : members ≠ [])
    (R : ℕ) (hr : ∀ s i, (draw s i).2 ≤ R) :
    (sampledGroupActionSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) members hne).1 ∧
    (sampledGroupActionSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤
      (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) members hne).2 * (R + 4) := by
  have h := chooseUnskippedSourceWithWork_eq_cost source target parent b P exponent Q tau F
    child initial current scales draw members hne R hr
  let finish := fun selected : Member =>
    let rounded := roundedBandReadWithWork exponent b selected.actions selected.nonempty initial
    let result := endpointActionWithWork selected.center rounded.1.get
    (result.1, rounded.2 + result.2)
  change (finish (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F
      child initial current scales draw members hne).1).1 =
      (finish (chooseUnskippedReadWithWork source target parent b P exponent Q tau F
        child initial current scales (fun s i => (draw s i).1) members hne).1).1 ∧ _
  have hf := congrArg finish h.1
  refine ⟨congrArg Prod.fst hf, ?_⟩
  have hcost : (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F
      child initial current scales draw members hne).2 +
      (finish (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F
        child initial current scales draw members hne).1).2 + 3 ≤
      ((chooseUnskippedReadWithWork source target parent b P exponent Q tau F
        child initial current scales (fun s i => (draw s i).1) members hne).2 +
        (finish (chooseUnskippedReadWithWork source target parent b P exponent Q tau F
          child initial current scales (fun s i => (draw s i).1) members hne).1).2 + 3) * (R + 4) := by
    rw [hf]
    nlinarith only [h.2]
  simpa only [sampledGroupActionSourceWithWork, sampledGroupActionReadWithWork, finish,
    Nat.add_assoc] using hcost


theorem sampledGroupActionSourceWithWork_value (members : List Member) (hne : members ≠ []) :
    (sampledGroupActionSourceWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
        scales (fun s i => (draw s i).1) members hne).1 := by
  let finish := fun selected : Member =>
    let rounded := roundedBandReadWithWork exponent b selected.actions selected.nonempty initial
    (endpointActionWithWork selected.center rounded.1.get).1
  change finish (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F
      child initial current scales draw members hne).1 =
      finish (chooseUnskippedReadWithWork source target parent b P exponent Q tau F
        child initial current scales (fun s i => (draw s i).1) members hne).1
  exact congrArg finish (chooseUnskippedSourceWithWork_value source target parent b P exponent Q
    tau F child initial current scales draw members hne)


end Group
end EditApproximation.BinaryFraction

end OAI
