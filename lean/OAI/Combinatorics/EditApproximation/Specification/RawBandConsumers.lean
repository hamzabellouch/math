import OAI.Combinatorics.EditApproximation.Specification.RawBand
import OAI.Combinatorics.EditApproximation.Definitions

namespace OAI.EditApproximation.BinaryFraction

section Group
variable {ny M T : ℕ} (b exponent Q : ℕ)
  (initial current : Fin M → TargetInterval ny → BinaryFraction × ℕ)
  (initialAllocation currentAllocation : Fin M → TargetInterval ny → ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)
  (drawSource : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)
  (drawAllocation : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → ℕ)

def unskippedEstimateReadWithWorkRaw (member : (RawUnskippedBand M ny)) : BinaryFraction × ℕ :=
  let mass := envelopeVectorReadWithWork b member.actions initial
  let rounded := roundedBandReadWithWork exponent b member.actions member.nonempty initial
  let values := vectorMapWithWork M fun i => current i (rounded.1.get i)
  let connection := endpointConnectionWithWork member.center rounded.1.get
  let result := countedGroupMemberWithWork Q b scales connection.1 mass.1 values.1 draw
  (result.1, mass.2 + rounded.2 + values.2 + connection.2 + result.2 + 5)

def chooseUnskippedReadWithWorkRaw (members : List (RawUnskippedBand M ny)) (hne : members ≠ []) : (RawUnskippedBand M ny) × ℕ :=
  selectGroupWithWork members hne
    (unskippedEstimateReadWithWorkRaw b exponent Q initial current scales draw)

def sampledGroupActionReadWithWorkRaw (members : List (RawUnskippedBand M ny)) (hne : members ≠ []) :
    BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M × ℕ :=
  let selected := chooseUnskippedReadWithWorkRaw b exponent Q initial current scales draw members hne
  let rounded := roundedBandReadWithWork exponent b selected.1.actions selected.1.nonempty initial
  let result := endpointActionWithWork selected.1.center rounded.1.get
  (result.1, selected.2 + rounded.2 + result.2 + 3)













end Group

end OAI.EditApproximation.BinaryFraction
