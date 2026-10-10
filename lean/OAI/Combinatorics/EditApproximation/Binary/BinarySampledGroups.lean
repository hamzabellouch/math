import OAI.Combinatorics.EditApproximation.Binary.BinaryCountedGroupWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryPhysicalContinuation
import OAI.Combinatorics.EditApproximation.Geometry.CellGroupSelection

namespace OAI

/-! The sampled group continuation uses the executed envelopes, rounded
states, exact finite sample counts, and ordered minimizing scan. Its output
is the same physical action as the group program used by the accuracy proof. -/

namespace EditApproximation
namespace BinaryFraction

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ) (hb : 0 < b)
  (tau F : BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q)) (fun i q => BinaryFraction.value (initial i q))

def unskippedEstimateWithWork (member : Member) : BinaryFraction × ℕ :=
  let mass := envelopeVectorWithWork b member.actions initial
  let rounded := roundedBandWithWork exponent b member.actions member.nonempty initial
  let values := vectorMapWithWork M fun i => (current i (rounded.1.get i), 1)
  let connection := endpointConnectionWithWork member.center rounded.1.get
  let result := countedGroupMemberWithWork Q b scales connection.1 mass.1 values.1 draw
  (result.1, mass.2 + rounded.2 + values.2 + connection.2 + result.2 + 5)

include hb in
theorem unskippedEstimateWithWork_value (member : Member) :
    (unskippedEstimateWithWork source target parent b P exponent Q tau F child initial current scales draw member).1.value =
      unskippedGroupEstimate (fun t => (scales t).value)
        (fun t => groupSampleCount M Q b (scales t).value)
        (fun i q => (current i q).value) member draw := by
  have hround : (roundedBandWithWork exponent b member.actions member.nonempty initial).1.get =
      member.rounded := roundedBandWithWork_value exponent b member.actions member.nonempty initial hb
  have hmass (i : Fin M) : ((envelopeVectorWithWork b member.actions initial).1.get i).value =
      member.envelope i := envelopeVectorWithWork_value b member.actions initial hb i
  simp only [unskippedEstimateWithWork, countedGroupMemberWithWork_value,
    endpointConnectionWithWork_value, vectorMapWithWork_value, hround, hmass, unskippedGroupEstimate]

def chooseBinaryUnskippedWithWork (members : List Member) (hne : members ≠ []) : Member × ℕ :=
  selectGroupWithWork members hne
    (unskippedEstimateWithWork source target parent b P exponent Q tau F child initial current scales draw)

include hb in
theorem chooseBinaryUnskippedWithWork_value (members : List Member) (hne : members ≠ []) :
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1 = selectGroupMember members hne (fun member =>
        unskippedGroupEstimate (fun t => (scales t).value)
          (fun t => groupSampleCount M Q b (scales t).value)
          (fun i q => (current i q).value) member draw) := by
  simp only [chooseBinaryUnskippedWithWork, selectGroupWithWork_value,
    unskippedEstimateWithWork_value source target parent b P exponent Q hb tau F child initial current scales draw]

def sampledGroupActionWithWork (members : List Member) (hne : members ≠ []) :
    BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M × ℕ :=
  let selected := chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F
    child initial current scales draw members hne
  let rounded := roundedBandWithWork exponent b selected.1.actions selected.1.nonempty initial
  let result := endpointActionWithWork selected.1.center rounded.1.get
  (result.1, selected.2 + rounded.2 + result.2 + 3)

include hb in
theorem sampledGroupActionWithWork_value (members : List Member) (hne : members ≠ []) :
    (sampledGroupActionWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).1.decode =
      (selectGroupMember members hne (fun member =>
        unskippedGroupEstimate (fun t => (scales t).value)
          (fun t => groupSampleCount M Q b (scales t).value)
          (fun i q => (current i q).value) member draw)).rationalAction := by
  let selected : Member := (chooseBinaryUnskippedWithWork source target parent b P exponent Q
    tau F child initial current scales draw members hne).1
  have hround := roundedBandWithWork_value exponent b selected.actions selected.nonempty initial hb
  have haction : (endpointActionWithWork selected.center
      (roundedBandWithWork exponent b selected.actions selected.nonempty initial).1.get).1.decode =
      selected.rationalAction := by
    exact (endpointActionWithWork_decode _ _).trans (congrArg
      (fun states : Fin M → TargetInterval target.length =>
        (⟨selected.center, endpointActionConnection selected.center states, fun i => (i, states i)⟩ :
          PhysicalRationalAction M target.length)) hround)
  exact haction.trans (congrArg UnskippedBand.rationalAction
    (chooseBinaryUnskippedWithWork_value source target parent b P exponent Q hb tau F
      child initial current scales draw members hne))

end Group
end BinaryFraction
end EditApproximation

end OAI
