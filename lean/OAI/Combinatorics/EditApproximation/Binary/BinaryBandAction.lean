import OAI.Combinatorics.EditApproximation.Binary.BinaryActionSelection
import OAI.Combinatorics.EditApproximation.Binary.BinaryActualBandOptimizer

namespace OAI

/-! Materialized Boolean vertices retain their band labels. The resulting
selected action, including every tie, is the action used by the online
sampler in the accuracy development. -/

namespace EditApproximation
namespace BinaryFraction

def labeledBandVerticesWithWork {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) : List ((Fin M → σ) × Vector BinaryFraction d) × ℕ :=
  let total := bandMassTotalWithWork mass
  let vertices := band.map fun action =>
    let vertex := vectorMapWithWork d fun i =>
      bandCoordinateWithWork mass total.1 action (coordinates.get i)
    ((action, vertex.1), vertex.2)
  (vertices.map Prod.fst, total.2 + (vertices.map Prod.snd).sum + 8 * band.length)

theorem labeledBandVerticesWithWork_vectors {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) :
    (labeledBandVerticesWithWork coordinates mass band).1.map Prod.snd =
      (bandVerticesWithWork coordinates mass band).1 := by
  simp only [labeledBandVerticesWithWork, bandVerticesWithWork, List.map_map, Function.comp_def]

theorem labeledBandVerticesWithWork_values {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) :
    (labeledBandVerticesWithWork coordinates mass band).1.map
        (fun pair => (pair.1, pair.2.map value)) =
      band.map (fun action => (action,
        restrictOptimizerVector coordinates (actionVector (fun j => (mass.get j).value) action))) := by
  simp only [labeledBandVerticesWithWork, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro action _
  apply Prod.ext
  · rfl
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  change ((vectorMapWithWork (α := BinaryFraction) d _).1.get ⟨i, hi⟩).value =
    (restrictOptimizerVector coordinates (actionVector (fun j => (mass.get j).value) action)).get ⟨i, hi⟩
  rw [vectorMapWithWork_value, bandCoordinateWithWork_value, restrictOptimizerVector_get]

theorem labeledBandVerticesWithWork_cost {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) :
    (labeledBandVerticesWithWork coordinates mass band).2 =
      (bandVerticesWithWork coordinates mass band).2 + 2 * band.length := by
  simp only [labeledBandVerticesWithWork, bandVerticesWithWork, List.map_map, Function.comp_def]
  omega

def preparedBandActionWithWork {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (table : ℕ → Fin M × σ → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → σ)) (G j t : ℕ) :
    Option (Fin M → σ) × ℕ :=
  let coordinates := listedBandCoordinateVector band
  let vertices := labeledBandVerticesWithWork coordinates mass band
  let linear := vectorMapWithWork _ fun i =>
    onlineLinearWithWork (fun j => mass.get j) table eta kappa t (coordinates.get i)
  let selected := selectionWithWork vertices.1 linear.1 G j
  (selected.1, vertices.2 + linear.2 + selected.2 + 2)

theorem preparedBandActionWithWork_value {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (table : ℕ → Fin M × σ → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → σ)) (hband : band ≠ []) (G j t : ℕ) :
    (preparedBandActionWithWork mass table eta kappa band G j t).1.getD (band.head hband) =
      finiteOptimizerAction band hband (fun i => (mass.get i).value)
        (rationalOnlineLinear eta.value kappa.value
          (childGain (fun i => (mass.get i).value) (fun s i => (table s i).value))
          (childDecrement (fun i => (mass.get i).value) (fun s i => (table s i).value)) t) G j := by
  let coordinates := listedBandCoordinateVector band
  let linear := rationalOnlineLinear eta.value kappa.value
    (childGain (fun i => (mass.get i).value) (fun s i => (table s i).value))
    (childDecrement (fun i => (mass.get i).value) (fun s i => (table s i).value)) t
  have hl : (vectorMapWithWork _ (fun i => onlineLinearWithWork
      (fun k => mass.get k) table eta kappa t (coordinates.get i))).1.map value =
        restrictOptimizerVector coordinates linear := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    change ((vectorMapWithWork (α := BinaryFraction) _ _).1.get ⟨i, hi⟩).value =
      (restrictOptimizerVector coordinates linear).get ⟨i, hi⟩
    rw [vectorMapWithWork_value, onlineLinearWithWork_value, restrictOptimizerVector_get]
  change (selectionWithWork (labeledBandVerticesWithWork coordinates mass band).1
    (vectorMapWithWork _ (fun i => onlineLinearWithWork
      (fun k => mass.get k) table eta kappa t (coordinates.get i))).1 G j).1.getD _ = _
  rw [selectionWithWork_value, labeledBandVerticesWithWork_values, hl]
  exact materializedBandActionWithWork_value band hband (fun i => (mass.get i).value) linear G j

def preparedBandActionBitBudget (M d vertices G K t Be Bk Bm Bt E : ℕ) : ℕ :=
  bandPreparationBitBudget M d vertices Bm + 2 * vertices +
    d * (onlineLinearBitBudget Be Bk Bm Bt t + 6) +
    selectionBitBudget d vertices G K (bandVertexWordBudget M Bm) (bandVertexWordBudget M Bm)
      (onlineLinearStorageBudget Be Bk Bm Bt t) (E * (2 * t + 1)) + 2

theorem preparedBandActionWithWork_cost {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (table : ℕ → Fin M × σ → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → σ)) (G K t Be Bk Bm Bt E : ℕ)
    (hband : band ≠ []) (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk)
    (hm : ∀ j, (mass.get j).width ≤ Bm) (hmpos : ∀ j, 0 < (mass.get j).value)
    (ht : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (table s ((listedBandCoordinateVector band).get i)).width ≤ Bt)
    (heabs : |eta.value| ≤ E) (hkrange : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (htrange : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      0 ≤ (table s ((listedBandCoordinateVector band).get i)).value ∧
        (table s ((listedBandCoordinateVector band).get i)).value ≤
          (mass.get ((listedBandCoordinateVector band).get i).1).value) :
    (preparedBandActionWithWork mass table eta kappa band G K t).2 ≤
      preparedBandActionBitBudget M (listedBandCoordinates band).length band.length G K t Be Bk Bm Bt E := by
  let coordinates := listedBandCoordinateVector band
  let vertices := (labeledBandVerticesWithWork coordinates mass band).1
  let linear := (vectorMapWithWork _ fun i =>
    onlineLinearWithWork (fun j => mass.get j) table eta kappa t (coordinates.get i)).1
  have hlength : vertices.length = band.length := by
    simp only [vertices, labeledBandVerticesWithWork, List.length_map]
  have hvertices : vertices ≠ [] := by
    intro h
    rw [h, List.length_nil] at hlength
    exact hband (List.length_eq_zero_iff.mp hlength.symm)
  have hv (v : (Fin M → σ) × Vector BinaryFraction (listedBandCoordinates band).length)
      (hmem : v ∈ vertices) (i : Fin (listedBandCoordinates band).length) :=
    bandVerticesWithWork_input_bounds coordinates mass band Bm hm hmpos v.2
      (by rw [← labeledBandVerticesWithWork_vectors]
          exact List.mem_map.mpr ⟨v, hmem, rfl⟩) i
  have hlwidth (i : Fin (listedBandCoordinates band).length) :
      (linear.get i).width ≤ onlineLinearStorageBudget Be Bk Bm Bt t := by
    simp only [linear, vectorMapWithWork_value]
    exact onlineLinearWithWork_storage (fun j => mass.get j) table eta kappa t
      (coordinates.get i) Be Bk Bm Bt he hk (hm _) (fun s hs => ht s hs i)
  have hlvalue (i : Fin (listedBandCoordinates band).length) :
      |(linear.get i).value| ≤ (E * (2 * t + 1) : ℕ) := by
    simp only [linear, vectorMapWithWork_value, onlineLinearWithWork_value]
    have h := rationalOnlineLinear_abs (fun j => (mass.get j).value)
      (fun s j => (table s j).value) eta.value kappa.value t E (coordinates.get i)
      heabs (hmpos _) hkrange (fun s hs => htrange s hs i)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using h
  have hc := selectionWithWork_cost vertices linear G K (bandVertexWordBudget M Bm)
    (bandVertexWordBudget M Bm) (onlineLinearStorageBudget Be Bk Bm Bt t) (E * (2 * t + 1))
    hvertices (fun v hv' i => ⟨(hv v hv' i).1, (hv v hv' i).2.1, (hv v hv' i).2.2.1⟩)
    (fun v hv' i => (hv v hv' i).2.2.2) hlwidth hlvalue
  rw [hlength] at hc
  have hp := bandVerticesWithWork_cost coordinates mass band Bm hm
  have hl := vectorMapWithWork_cost_le _
    (fun i => onlineLinearWithWork (fun j => mass.get j) table eta kappa t (coordinates.get i))
    (onlineLinearBitBudget Be Bk Bm Bt t) (fun i => onlineLinearWithWork_cost
      (fun j => mass.get j) table eta kappa t (coordinates.get i) Be Bk Bm Bt
      he hk (hm _) (fun s hs => ht s hs i))
  change (labeledBandVerticesWithWork coordinates mass band).2 +
    (vectorMapWithWork _ (fun i => onlineLinearWithWork (fun j => mass.get j)
      table eta kappa t (coordinates.get i))).2 +
    (selectionWithWork vertices linear G K).2 + 2 ≤ _
  rw [labeledBandVerticesWithWork_cost]
  unfold preparedBandActionBitBudget
  omega

def bandActionWithWork {M ny : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval ny)) (G j t : ℕ) :
    Option (Fin M → TargetInterval ny) × ℕ :=
  let mass := envelopeVectorWithWork b band initial
  let selected := preparedBandActionWithWork mass.1 table eta kappa band G j t
  (selected.1, mass.2 + selected.2 + 1)

theorem bandActionWithWork_value {M ny : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval ny))
    (hband : band ≠ []) (G j t : ℕ) (hb : 0 < b) :
    (bandActionWithWork b initial table eta kappa band G j t).1.getD (band.head hband) =
      finiteOptimizerAction band hband (bandChildEnvelope b band (fun i q => (initial i q).value))
        (rationalOnlineLinear eta.value kappa.value
          (childGain (bandChildEnvelope b band (fun i q => (initial i q).value))
            (fun s i => (table s i).value))
          (childDecrement (bandChildEnvelope b band (fun i q => (initial i q).value))
            (fun s i => (table s i).value)) t) G j := by
  change (preparedBandActionWithWork (envelopeVectorWithWork b band initial).1
    table eta kappa band G j t).1.getD _ = _
  rw [preparedBandActionWithWork_value]
  have hm : (fun i => ((envelopeVectorWithWork b band initial).1.get i).value) =
      bandChildEnvelope b band (fun i q => (initial i q).value) := by
    funext i
    exact envelopeVectorWithWork_value b band initial hb i
  rw [hm]

def bandActionBitBudget (M d b vertices G K t Be Bk Bi Bt E : ℕ) : ℕ :=
  M * (bandEnvelopeBitBudget b M vertices Bi + 6) +
    preparedBandActionBitBudget M d vertices G K t Be Bk
      (3 * bandEnvelopeWordBudget b M Bi + 1) Bt E + 1

theorem bandActionWithWork_cost {M ny : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval ny))
    (G K t Be Bk Bi Bt E : ℕ) (hband : band ≠ []) (hb : 0 < b) (hM : 0 < M)
    (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk)
    (hi : ∀ action ∈ band, ∀ j, (initial j (action j)).width ≤ Bi)
    (ht : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (table s ((listedBandCoordinateVector band).get i)).width ≤ Bt)
    (heabs : |eta.value| ≤ E) (hkrange : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (htrange : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      0 ≤ (table s ((listedBandCoordinateVector band).get i)).value ∧
        (table s ((listedBandCoordinateVector band).get i)).value ≤
          (initial ((listedBandCoordinateVector band).get i).1
            ((listedBandCoordinateVector band).get i).2).value) :
    (bandActionWithWork b initial table eta kappa band G K t).2 ≤
      bandActionBitBudget M (listedBandCoordinates band).length b band.length G K t Be Bk Bi Bt E := by
  let coordinates := listedBandCoordinateVector band
  let mass := (envelopeVectorWithWork b band initial).1
  have hmv (j : Fin M) : (mass.get j).value =
      bandChildEnvelope b band (fun k q => (initial k q).value) j :=
    envelopeVectorWithWork_value b band initial hb j
  have hm (j : Fin M) : (mass.get j).width ≤ 3 * bandEnvelopeWordBudget b M Bi + 1 := by
    simp only [mass, envelopeVectorWithWork, vectorMapWithWork_value]
    exact bandEnvelopeWithWork_width b band initial j Bi (fun action ha => hi action ha j)
  have hmpos (j : Fin M) : 0 < (mass.get j).value := by
    rw [hmv]
    exact lt_of_lt_of_le (div_pos (by exact_mod_cast hb) (by exact_mod_cast hM))
      (bandChildEnvelope_lower b band (fun j q => (initial j q).value) j).1
  have hnormalized (s : ℕ) (hs : s ≤ t + 1) (i : Fin (listedBandCoordinates band).length) :
      0 ≤ (table s (coordinates.get i)).value ∧
        (table s (coordinates.get i)).value ≤ (mass.get (coordinates.get i).1).value := by
    refine ⟨(htrange s hs i).1, ?_⟩
    obtain ⟨action, ha, heq⟩ := listedBandCoordinateVector_coverage band i
    have henv := (bandChildEnvelope_lower b band (fun j q => (initial j q).value)
      (coordinates.get i).1).2 action ha
    rw [heq] at henv
    rw [hmv]
    exact (htrange s hs i).2.trans henv
  have hp := preparedBandActionWithWork_cost mass table eta kappa band G K t
    Be Bk (3 * bandEnvelopeWordBudget b M Bi + 1) Bt E hband he hk hm hmpos ht heabs hkrange hnormalized
  have hc := vectorMapWithWork_cost_le M (bandEnvelopeWithWork b band initial)
    (bandEnvelopeBitBudget b M band.length Bi)
    (fun j => bandEnvelopeWithWork_cost b band initial j Bi (fun action ha => hi action ha j))
  change (envelopeVectorWithWork b band initial).2 +
    (preparedBandActionWithWork mass table eta kappa band G K t).2 + 1 ≤ _
  change (envelopeVectorWithWork b band initial).2 ≤ _ at hc
  unfold bandActionBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
