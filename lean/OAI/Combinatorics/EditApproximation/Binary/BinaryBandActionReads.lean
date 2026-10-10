import OAI.Combinatorics.EditApproximation.Binary.BinaryOnlineReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandAction
import OAI.Combinatorics.EditApproximation.Binary.BinaryCoordinateAction
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The actual labelled online action, with charged initial and history reads. -/

namespace EditApproximation
namespace BinaryFraction

def preparedBandActionReadWithWork {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (read : ℕ → Fin M × σ → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → σ)) (G j t : ℕ) :
    Option (Fin M → σ) × ℕ :=
  let coordinates := listedBandCoordinateVector band
  let vertices := labeledBandVerticesWithWork coordinates mass band
  let linear := vectorMapWithWork _ fun i =>
    onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t (coordinates.get i)
  let selected := selectionWithWork vertices.1 linear.1 G j
  (selected.1, vertices.2 + linear.2 + selected.2 + 2)

theorem preparedBandActionReadWithWork_eq_cost {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (read : ℕ → Fin M × σ → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → σ)) (G j t R : ℕ)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (preparedBandActionReadWithWork mass read eta kappa band G j t).1 =
      (preparedBandActionWithWork mass (fun s i => (read s i).1) eta kappa band G j t).1 ∧
    (preparedBandActionReadWithWork mass read eta kappa band G j t).2 ≤
      (preparedBandActionWithWork mass (fun s i => (read s i).1) eta kappa band G j t).2 +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hl := vectorMapWithWork_extra (listedBandCoordinates band).length
    (fun i => onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t
      ((listedBandCoordinateVector band).get i))
    (fun i => onlineLinearWithWork (fun j => mass.get j) (fun s k => (read s k).1) eta kappa t
      ((listedBandCoordinateVector band).get i))
    ((3 * t + 1) * R)
    (fun i => (onlineLinearReadWithWork_eq_cost _ read eta kappa t _ R
      (fun s hs => hr s hs i)).1)
    (fun i => (onlineLinearReadWithWork_eq_cost _ read eta kappa t _ R
      (fun s hs => hr s hs i)).2)
  unfold preparedBandActionReadWithWork preparedBandActionWithWork
  dsimp only
  rw [hl.1]
  exact ⟨rfl, by omega⟩

def bandActionReadWithWork {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t : ℕ) :
    Option (Fin M → TargetInterval n) × ℕ :=
  let mass := envelopeVectorReadWithWork b band initial
  let selected := preparedBandActionReadWithWork mass.1 read eta kappa band G j t
  (selected.1, mass.2 + selected.2 + 1)

theorem bandActionReadWithWork_eq_cost {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t R C : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ C)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (bandActionReadWithWork b initial read eta kappa band G j t).1 =
      (bandActionWithWork b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band G j t).1 ∧
    (bandActionReadWithWork b initial read eta kappa band G j t).2 ≤
      (bandActionWithWork b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band G j t).2 +
        M * (band.length * (C + 3)) +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hm := envelopeVectorReadWithWork_eq_cost b band initial C hi
  have hs := preparedBandActionReadWithWork_eq_cost
    (envelopeVectorWithWork b band (fun i q => (initial i q).1)).1 read
    eta kappa band G j t R hr
  unfold bandActionReadWithWork bandActionWithWork
  dsimp only
  rw [hm.1]
  exact ⟨hs.1, by omega⟩

def sampledOnlineActionReadWithWork {n M : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    BinaryBellmanAction (TargetInterval n) (Fin M × TargetInterval n) M × ℕ :=
  let chosen := triangularChoiceWithWork K integer
  let selected := bandActionReadWithWork b initial read eta kappa band G chosen.1.val t
  let states := selected.1.getD (band.head hne)
  (⟨center, zero, fun i => (i, states i)⟩, chosen.2 + selected.2 + M + 2)

theorem sampledOnlineActionReadWithWork_eq_cost {n M : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t R C : ℕ) (integer : Fin (optimizerTriangularMass K))
    (hi : ∀ i q, (initial i q).2 ≤ C)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (sampledOnlineActionReadWithWork center b initial read eta kappa band hne G K t integer).1 =
      (sampledOnlineActionWithWork center b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band hne G K t integer).1 ∧
    (sampledOnlineActionReadWithWork center b initial read eta kappa band hne G K t integer).2 ≤
      (sampledOnlineActionWithWork center b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band hne G K t integer).2 +
        M * (band.length * (C + 3)) +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hs := bandActionReadWithWork_eq_cost b initial read eta kappa band G
    (triangularChoiceWithWork K integer).1.val t R C hi hr
  unfold sampledOnlineActionReadWithWork sampledOnlineActionWithWork
  dsimp only
  rw [hs.1]
  exact ⟨rfl, by omega⟩




theorem countedPreparedActionReadWithWork_eq_cost {M n : ℕ} (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t R : ℕ)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedPreparedActionReadWithWork mass read eta kappa band G j t).1 =
      (countedPreparedActionWithWork mass (fun s i => (read s i).1) eta kappa band G j t).1 ∧
    (countedPreparedActionReadWithWork mass read eta kappa band G j t).2 ≤
      (countedPreparedActionWithWork mass (fun s i => (read s i).1) eta kappa band G j t).2 +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hl := vectorMapWithWork_extra (listedBandCoordinates band).length
    (fun i => onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t
      ((listedBandCoordinateVector band).get i))
    (fun i => onlineLinearWithWork (fun j => mass.get j) (fun s k => (read s k).1) eta kappa t
      ((listedBandCoordinateVector band).get i))
    ((3 * t + 1) * R)
    (fun i => (onlineLinearReadWithWork_eq_cost _ read eta kappa t _ R
      (fun s hs => hr s hs i)).1)
    (fun i => (onlineLinearReadWithWork_eq_cost _ read eta kappa t _ R
      (fun s hs => hr s hs i)).2)
  unfold countedPreparedActionReadWithWork countedPreparedActionWithWork
  simp only [coordinateVectorWithWork_value]
  rw [hl.1]
  exact ⟨rfl, by omega⟩



theorem countedBandActionReadWithWork_eq_cost {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t R C : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ C)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedBandActionReadWithWork b initial read eta kappa band G j t).1 =
      (countedBandActionWithWork b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band G j t).1 ∧
    (countedBandActionReadWithWork b initial read eta kappa band G j t).2 ≤
      (countedBandActionWithWork b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band G j t).2 +
        M * (band.length * (C + 3)) +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hm := envelopeVectorReadWithWork_eq_cost b band initial C hi
  have hs := countedPreparedActionReadWithWork_eq_cost
    (envelopeVectorWithWork b band (fun i q => (initial i q).1)).1 read
    eta kappa band G j t R hr
  unfold countedBandActionReadWithWork countedBandActionWithWork
  dsimp only
  rw [hm.1]
  exact ⟨hs.1, by omega⟩



theorem countedSampledOnlineReadWithWork_eq_cost {n M : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t R C : ℕ) (integer : Fin (optimizerTriangularMass K))
    (hi : ∀ i q, (initial i q).2 ≤ C)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedSampledOnlineReadWithWork center b initial read eta kappa band hne G K t integer).1 =
      (countedSampledOnlineWithWork center b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band hne G K t integer).1 ∧
    (countedSampledOnlineReadWithWork center b initial read eta kappa band hne G K t integer).2 ≤
      (countedSampledOnlineWithWork center b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band hne G K t integer).2 +
        M * (band.length * (C + 3)) +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hs := countedBandActionReadWithWork_eq_cost b initial read eta kappa band G
    (triangularChoiceWithWork K integer).1.val t R C hi hr
  unfold countedSampledOnlineReadWithWork countedSampledOnlineWithWork
  dsimp only
  rw [hs.1]
  exact ⟨rfl, by omega⟩

end BinaryFraction
end EditApproximation

end OAI
