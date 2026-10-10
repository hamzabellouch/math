import OAI.Combinatorics.EditApproximation.Binary.BinaryContinuationWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryWideChildWork
import OAI.Combinatorics.EditApproximation.Geometry.LocalWideStep
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The local refinement return is computed by the binary-fraction
continuation. Wide actions are built from the emitted endpoint grids, and
their connection charges are evaluated before the two Bellman minima. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem endpointActionWithWork_decode {ny M : ℕ} (center : TargetInterval ny)
    (states : Fin M → TargetInterval ny) :
    (endpointActionWithWork center states).1.decode =
      (⟨center, endpointActionConnection center states, fun i => (i, states i)⟩ :
        PhysicalRationalAction M ny) := by
  simp only [endpointActionWithWork, BinaryBellmanAction.decode, endpointConnectionWithWork_value]



@[simp] theorem wideActionsFromRepresentativesWithWork_decode {nx ny : ℕ} (M : ℕ)
    (parent : TargetInterval nx) (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (hP : 0 < P) :
    ((wideActionsFromRepresentativesWithWork M parent representatives P).1.map
      BinaryBellmanAction.decode) = rationalActualWideActions parent representatives P := by
  simp only [wideActionsFromRepresentativesWithWork, arithmeticFlatMapWithWork_value,
    List.map_flatMap, arithmeticMapWithWork_value, List.map_map, Function.comp_def,
    endpointActionWithWork_decode, rationalActualWideActions]
  apply List.flatMap_congr
  intro br _
  rw [← wideActionGridWithWork_value M parent br.2 br.1 P hP, List.map_map]
  rfl

def physicalContinuationWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P F : ℕ)
    (delta fallback : BinaryFraction)
    (old current : Fin M × TargetInterval ny → BinaryFraction)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (query : TargetInterval ny) : BinaryFraction × ℕ :=
  let wide := wideActionsFromRepresentativesWithWork M parent representatives P
  let L := canonicalMulWithWork (nat 128) (nat F)
  let result := localContinuationWithWork endpointDistanceWithWork L.1 delta fallback
    old current query wide.1 groups online
  (result.1, wide.2 + L.2 + result.2 + 1)

theorem physicalContinuationWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P F : ℕ)
    (delta fallback : BinaryFraction)
    (old current : Fin M × TargetInterval ny → BinaryFraction)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (query : TargetInterval ny) (hP : 0 < P) :
    (physicalContinuationWithWork parent representatives P F delta fallback old current groups online query).1.value =
      rationalWideStep parent representatives P (fun _ => fallback.value) (128 * F) delta.value
        (fun s => (old s).value) (fun s => (current s).value)
        (groups.map BinaryBellmanAction.decode) (online.map BinaryBellmanAction.decode) query := by
  simp only [physicalContinuationWithWork, localContinuationWithWork_value,
    wideActionsFromRepresentativesWithWork_decode M parent representatives P hP,
    endpointDistanceWithWork_value, canonicalMulWithWork_value, nat_value]
  rfl

/-- Exact local-program wiring. The two equalities are representation
identities for the already-computed sampled action lists. -/
theorem physicalContinuationWithWork_local_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ)
    (tau a : ℚ) (delta : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (childMass childInitial : Fin M → TargetInterval target.length → ℚ)
    (old current : Fin M × TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q)
    (groups online : List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M))
    (logicalOnline : List (PhysicalRationalAction M target.length)) (query : TargetInterval target.length)
    (hP : 0 < P)
    (hgroups : groups.map BinaryBellmanAction.decode = localCellGroupActions source target parent
      N P F exponent Q tau a (fun r => (parentInitial r).value) childMass childInitial
      (fun i r => (current (i, r)).value) draw query)
    (honline : online.map BinaryBellmanAction.decode = logicalOnline) :
    (physicalContinuationWithWork parent
      (localRefinementRepresentatives N P F a (fun r => (parentInitial r).value) query)
      P F delta (parentInitial query) old current groups online query).1.value =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta.value
      (fun r => (parentInitial r).value) childMass childInitial
      (fun i r => (old (i, r)).value) (fun i r => (current (i, r)).value) draw logicalOnline query := by
  rw [physicalContinuationWithWork_value _ _ _ _ _ _ _ _ _ _ _ hP, hgroups, honline]
  rfl

end BinaryFraction
end EditApproximation

end OAI
