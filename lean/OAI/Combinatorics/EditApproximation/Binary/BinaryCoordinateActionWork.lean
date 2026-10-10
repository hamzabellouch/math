import OAI.Combinatorics.EditApproximation.Binary.BinaryCoordinateAction

namespace OAI

/-! The cost of coordinate construction and every endpoint equality is
added to the complete optimizer cost, with no unit-cost rational
or uncharged generic equality operation. -/

namespace EditApproximation
namespace BinaryFraction

private theorem vectorMap_cost_le_add {α β : Type*} (d : ℕ)
    (first : Fin d → α × ℕ) (second : Fin d → β × ℕ) (C : ℕ)
    (h : ∀ i, (first i).2 ≤ (second i).2 + C) :
    (vectorMapWithWork d first).2 ≤ (vectorMapWithWork d second).2 + d * C := by
  simp only [vectorMapWithWork, Vector.toList_map, Vector.toList_ofFn,
    List.map_ofFn, Function.comp_def, List.sum_ofFn]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hs
  omega

theorem countedBandVerticesWithWork_cost {M n d : ℕ}
    (coordinates : Vector (Fin M × TargetInterval n) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → TargetInterval n)) (B : ℕ)
    (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (countedBandVerticesWithWork coordinates mass band).2 ≤
      (labeledBandVerticesWithWork coordinates mass band).2 + band.length * d * (24 * B + 9) := by
  have hvertex (action : Fin M → TargetInterval n) :
      (vectorMapWithWork d (fun i => countedBandCoordinateWithWork mass
        (bandMassTotalWithWork mass).1 action (coordinates.get i))).2 ≤
      (vectorMapWithWork d (fun i => bandCoordinateWithWork mass
        (bandMassTotalWithWork mass).1 action (coordinates.get i))).2 + d * (24 * B + 9) := by
    apply vectorMap_cost_le_add
    intro i
    rw [(countedBandCoordinateWithWork_eq _ _ _ _).2]
    have hc := coordinateEqualWithWork_cost (coordinates.get i)
      ((coordinates.get i).1, action (coordinates.get i).1) B hM hn
    omega
  have hsum :
      (band.map (fun action => (vectorMapWithWork d (fun i => countedBandCoordinateWithWork mass
        (bandMassTotalWithWork mass).1 action (coordinates.get i))).2)).sum ≤
      (band.map (fun action => (vectorMapWithWork d (fun i => bandCoordinateWithWork mass
        (bandMassTotalWithWork mass).1 action (coordinates.get i))).2)).sum +
      band.length * (d * (24 * B + 9)) := by
    induction band with
    | nil => simp
    | cons action rest ih =>
      have ha := hvertex action
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  simp only [countedBandVerticesWithWork, labeledBandVerticesWithWork, List.map_map,
    Function.comp_def]
  simpa only [Nat.mul_assoc] using (show
    (bandMassTotalWithWork mass).2 + _ + 8 * band.length ≤
      (bandMassTotalWithWork mass).2 + _ + 8 * band.length + band.length * (d * (24 * B + 9)) by omega)

theorem countedPreparedActionWithWork_cost {M n : ℕ} (mass : Vector BinaryFraction M)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (G j t B : ℕ)
    (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (countedPreparedActionWithWork mass table eta kappa band G j t).2 ≤
      (preparedBandActionWithWork mass table eta kappa band G j t).2 +
      bandCoordinatesBitBudget M band.length B + (listedBandCoordinates band).length +
      band.length * (listedBandCoordinates band).length * (24 * B + 9) + 2 := by
  have hc := bandCoordinatesWithWork_cost band B hM hn
  have hv := countedBandVerticesWithWork_cost (listedBandCoordinateVector band) mass band B hM hn
  unfold countedPreparedActionWithWork
  simp only [coordinateVectorWithWork_value, countedBandVerticesWithWork_value]
  change (coordinateVectorWithWork band).2 +
    (countedBandVerticesWithWork (listedBandCoordinateVector band) mass band).2 + _ + _ + 3 ≤ _
  unfold coordinateVectorWithWork
  simp only [bandCoordinatesWithWork_value]
  unfold preparedBandActionWithWork
  dsimp only
  omega

theorem countedBandActionWithWork_cost {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (G j t B : ℕ)
    (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (countedBandActionWithWork b initial table eta kappa band G j t).2 ≤
      (bandActionWithWork b initial table eta kappa band G j t).2 +
      bandCoordinatesBitBudget M band.length B + (listedBandCoordinates band).length +
      band.length * (listedBandCoordinates band).length * (24 * B + 9) + 2 := by
  have h := countedPreparedActionWithWork_cost (envelopeVectorWithWork b band initial).1
    table eta kappa band G j t B hM hn
  unfold countedBandActionWithWork bandActionWithWork
  dsimp only
  omega

theorem countedSampledOnlineWithWork_cost {M n : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t B : ℕ) (integer : Fin (optimizerTriangularMass K))
    (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (countedSampledOnlineWithWork center b initial table eta kappa band hne G K t integer).2 ≤
      (sampledOnlineActionWithWork center b initial table eta kappa band hne G K t integer).2 +
      bandCoordinatesBitBudget M band.length B + (listedBandCoordinates band).length +
      band.length * (listedBandCoordinates band).length * (24 * B + 9) + 2 := by
  have h := countedBandActionWithWork_cost b initial table eta kappa band G
    (triangularChoiceWithWork K integer).1.val t B hM hn
  unfold countedSampledOnlineWithWork sampledOnlineActionWithWork
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI
