import OAI.Combinatorics.EditApproximation.Binary.BinaryBandCoordinates
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandAction
import OAI.Combinatorics.EditApproximation.Binary.BinarySampledOnline
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The prepared online action explicitly constructs its coordinate array
and compares stored endpoints when constructing each vertex. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem coordinateVectorWithWork_value {M n : ℕ} (band : List (Fin M → TargetInterval n)) :
    (coordinateVectorWithWork band).1 = listedBandCoordinateVector band := by
  unfold coordinateVectorWithWork listedBandCoordinateVector
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, List.get_eq_getElem]
  exact List.getElem_of_eq (bandCoordinatesWithWork_value band) _



theorem countedBandCoordinateWithWork_eq {M n : ℕ} (mass : Vector BinaryFraction M)
    (total : BinaryFraction) (action : Fin M → TargetInterval n)
    (coordinate : Fin M × TargetInterval n) :
    (countedBandCoordinateWithWork mass total action coordinate).1 =
      (bandCoordinateWithWork mass total action coordinate).1 ∧
    (countedBandCoordinateWithWork mass total action coordinate).2 =
      (coordinateEqualWithWork coordinate (coordinate.1, action coordinate.1)).2 +
      (bandCoordinateWithWork mass total action coordinate).2 + 1 := by
  have ht : (coordinateEqualWithWork coordinate (coordinate.1, action coordinate.1)).1 = true ↔
      coordinate.2 = action coordinate.1 := by
    rw [coordinateEqualWithWork_value]
    exact ⟨fun h => congrArg Prod.snd h, fun h => Prod.ext rfl h⟩
  unfold countedBandCoordinateWithWork bandCoordinateWithWork
  dsimp only
  by_cases h : coordinate.2 = action coordinate.1
  · simp only [ite_eq_left h, ite_eq_left (ht.mpr h), and_self]
  · simp only [ite_eq_right h, ite_eq_right (fun hp => h (ht.mp hp)), and_self]



@[simp] theorem countedBandVerticesWithWork_value {M n d : ℕ}
    (coordinates : Vector (Fin M × TargetInterval n) d)
    (mass : Vector BinaryFraction M) (band : List (Fin M → TargetInterval n)) :
    (countedBandVerticesWithWork coordinates mass band).1 =
      (labeledBandVerticesWithWork coordinates mass band).1 := by
  simp only [countedBandVerticesWithWork, labeledBandVerticesWithWork, List.map_map,
    Function.comp_def]
  apply List.map_congr_left
  intro action _
  apply congrArg (Prod.mk action)
  apply Vector.ext
  intro i hi
  change ((vectorMapWithWork d _).1.get ⟨i, hi⟩) = ((vectorMapWithWork d _).1.get ⟨i, hi⟩)
  rw [vectorMapWithWork_value, vectorMapWithWork_value]
  exact (countedBandCoordinateWithWork_eq _ _ _ _).1

def countedPreparedActionWithWork {M n : ℕ} (mass : Vector BinaryFraction M)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t : ℕ) :
    Option (Fin M → TargetInterval n) × ℕ :=
  let coordinates := coordinateVectorWithWork band
  let vertices := countedBandVerticesWithWork coordinates.1 mass band
  let linear := vectorMapWithWork _ fun i =>
    onlineLinearWithWork (fun child => mass.get child) table eta kappa t (coordinates.1.get i)
  let selected := selectionWithWork vertices.1 linear.1 G j
  (selected.1, coordinates.2 + vertices.2 + linear.2 + selected.2 + 3)

@[simp] theorem countedPreparedActionWithWork_value {M n : ℕ}
    (mass : Vector BinaryFraction M) (table : ℕ → Fin M × TargetInterval n → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t : ℕ) :
    (countedPreparedActionWithWork mass table eta kappa band G j t).1 =
      (preparedBandActionWithWork mass table eta kappa band G j t).1 := by
  simp only [countedPreparedActionWithWork, coordinateVectorWithWork_value,
    countedBandVerticesWithWork_value, preparedBandActionWithWork]

def countedBandActionWithWork {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (G j t : ℕ) :
    Option (Fin M → TargetInterval n) × ℕ :=
  let mass := envelopeVectorWithWork b band initial
  let selected := countedPreparedActionWithWork mass.1 table eta kappa band G j t
  (selected.1, mass.2 + selected.2 + 1)

@[simp] theorem countedBandActionWithWork_value {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (G j t : ℕ) :
    (countedBandActionWithWork b initial table eta kappa band G j t).1 =
      (bandActionWithWork b initial table eta kappa band G j t).1 := by
  simp only [countedBandActionWithWork, countedPreparedActionWithWork_value, bandActionWithWork]

def countedSampledOnlineWithWork {M n : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    BinaryBellmanAction (TargetInterval n) (Fin M × TargetInterval n) M × ℕ :=
  let chosen := triangularChoiceWithWork K integer
  let selected := countedBandActionWithWork b initial table eta kappa band G chosen.1.val t
  let states := selected.1.getD (band.head hne)
  (⟨center, zero, fun i => (i, states i)⟩, chosen.2 + selected.2 + M + 2)

@[simp] theorem countedSampledOnlineWithWork_value {M n : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    (countedSampledOnlineWithWork center b initial table eta kappa band hne G K t integer).1 =
      (sampledOnlineActionWithWork center b initial table eta kappa band hne G K t integer).1 := by
  simp only [countedSampledOnlineWithWork, countedBandActionWithWork_value, sampledOnlineActionWithWork]

end BinaryFraction
end EditApproximation

end OAI
