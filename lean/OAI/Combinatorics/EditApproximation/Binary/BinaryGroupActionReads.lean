import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryDyadicSampledGroups

namespace OAI

/-! The selected group action uses the same minimizing member and rounded
endpoints, while charging both the initial and current-table readers. -/

namespace EditApproximation
namespace BinaryFraction

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

def sampledGroupActionReadWithWork (members : List Member) (hne : members ≠ []) :
    BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M × ℕ :=
  let selected := chooseUnskippedReadWithWork source target parent b P exponent Q tau F
    child initial current scales draw members hne
  let rounded := roundedBandReadWithWork exponent b selected.1.actions selected.1.nonempty initial
  let result := endpointActionWithWork selected.1.center rounded.1.get
  (result.1, selected.2 + rounded.2 + result.2 + 3)

theorem sampledGroupActionReadWithWork_eq_cost (members : List Member) (hne : members ≠ []) (R C : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ C) (hr : ∀ i q, (current i q).2 ≤ R) :
    (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 =
      (sampledGroupActionWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1 ∧
    (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤
      (sampledGroupActionWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).2 +
      (members.map fun member => M * (member.actions.length * (C + 3)) +
        M * (member.actions.length * (C + 3)) + M * R).sum +
      M * (((chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.actions).length *
        (C + 3)) := by
  have hs := chooseUnskippedReadWithWork_eq_cost source target parent b P exponent Q tau F
    child initial current scales draw members hne R C hi hr
  have hp := roundedBandReadWithWork_eq_cost exponent b
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
      (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.actions
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
      (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.nonempty initial C hi
  unfold sampledGroupActionReadWithWork sampledGroupActionWithWork
  dsimp only
  simp only [hs.1, hp.1]
  exact ⟨trivial, by omega⟩

end Group

def dyadicSampledGroupActionReadWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent Q : ℕ) (tau F : BinaryFraction)
    (child : Fin M → TargetInterval target.length → BinaryFraction)
    (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b F.value)
    (draw : ∀ t : Fin (groupDyadicScales M b F.value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F.value t)) → Fin M)
    (members : List (UnskippedBand source target parent b P exponent tau.value F.value
      (fun i q => (child i q).value) (fun i q => (initial i q).1.value))) (hne : members ≠ []) :=
  sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
    (indexedGroupScales raw M b F.value hraw)
    (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
      (indexedGroupScales_value raw M b F.value hraw t)) j)) members hne

end BinaryFraction
end EditApproximation

end OAI
