import OAI.Combinatorics.EditApproximation.Numerics.GradientStorageBits
import OAI.Combinatorics.EditApproximation.Geometry.BandOptimizerWork
import OAI.Combinatorics.EditApproximation.Numerics.OptimizerWorkspace

namespace OAI

/-! The probability vectors actually stored for band actions have polynomial
encodings in the input child masses. No accuracy event is needed. -/

namespace EditApproximation

open Finset

def bandVertexEncodingBudget (M V B : ℕ) : ℕ :=
  B + (Nat.size (M * V) + 2 * (M * B + 1) + 1) + 3

theorem actionVector_encoding_le {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Fin M → ℚ) (action : Fin M → σ) (coordinate : Fin M × σ)
    (V B : ℕ) (habs : ∀ i, |mass i| ≤ V)
    (hbits : ∀ i, rationalEncodingBits (mass i) ≤ B) :
    rationalEncodingBits (actionVector mass action coordinate) ≤ bandVertexEncodingBudget M V B := by
  have hsum := rational_finite_sum_encoding_le (univ : Finset (Fin M)) mass V B
    (fun i _ => habs i) (fun i _ => (by
      unfold rationalEncodingBits at hbits
      have h := hbits i
      omega))
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  unfold actionVector
  split_ifs
  · have hdiv := rationalEncodingBits_div (mass coordinate.1) (∑ i, mass i)
    have hmass := hbits coordinate.1
    unfold bandVertexEncodingBudget
    omega
  · norm_num [rationalEncodingBits, bandVertexEncodingBudget]

theorem actionVector_zero_one {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Fin M → ℚ) (action : Fin M → σ) (coordinate : Fin M × σ)
    (hpos : ∀ i, 0 < mass i) :
    0 ≤ actionVector mass action coordinate ∧ actionVector mass action coordinate ≤ 1 := by
  have hsum : 0 < ∑ i, mass i :=
    (hpos coordinate.1).trans_le (Finset.single_le_sum (fun i _ => (hpos i).le) (mem_univ _))
  unfold actionVector
  split_ifs
  · exact ⟨(div_pos (hpos _) hsum).le,
      (div_le_one₀ hsum).2 (single_le_sum (fun i _ => (hpos i).le) (mem_univ _))⟩
  · norm_num

def storedBandVertices {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) (mass : Fin M → ℚ) :
    List (Vector ℚ (listedBandCoordinates band).length) :=
  band.map fun action => restrictOptimizerVector (listedBandCoordinateVector band) (actionVector mass action)

theorem storedBandVertices_nonempty {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) (mass : Fin M → ℚ) (hband : band ≠ []) :
    storedBandVertices band mass ≠ [] := by
  intro hempty
  exact hband (List.map_eq_nil_iff.mp hempty)

theorem storedBandVertices_input_bounds {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) (mass : Fin M → ℚ) (V B : ℕ)
    (hpos : ∀ i, 0 < mass i) (habs : ∀ i, |mass i| ≤ V)
    (hbits : ∀ i, rationalEncodingBits (mass i) ≤ B)
    (vertex : Vector ℚ (listedBandCoordinates band).length)
    (hvertex : vertex ∈ storedBandVertices band mass)
    (i : Fin (listedBandCoordinates band).length) :
    (0 ≤ vertex.get i ∧ vertex.get i ≤ 1) ∧
      Nat.size (vertex.get i).den ≤ bandVertexEncodingBudget M V B := by
  obtain ⟨action, _, rfl⟩ := List.mem_map.mp hvertex
  rw [restrictOptimizerVector_get]
  constructor
  · exact actionVector_zero_one mass action _ hpos
  · have h := actionVector_encoding_le mass action
      ((listedBandCoordinateVector band).get i) V B habs hbits
    unfold rationalEncodingBits at h
    omega

theorem storedBandOptimizer_history_bits {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) (hband : band ≠ []) (mass : Fin M → ℚ)
    (linear : Fin M × σ → ℚ) (G K V B : ℕ)
    (hpos : ∀ i, 0 < mass i) (habs : ∀ i, |mass i| ≤ V)
    (hbits : ∀ i, rationalEncodingBits (mass i) ≤ B) :
    rationalVectorListStorageBits (optimizerStoredHistory (storedBandVertices band mass)
      (restrictOptimizerVector (listedBandCoordinateVector band) linear) G K) ≤
      (K + 1) * ((listedBandCoordinates band).length *
        (2 * ((K + 1) * (2 * Nat.size (K + 1) + 2 + bandVertexEncodingBudget M V B) + 1) + 1)) := by
  exact optimizerStoredHistory_storage_le _ _ G K _ (storedBandVertices_nonempty band mass hband)
    (fun vertex hvertex i => storedBandVertices_input_bounds band mass V B hpos habs hbits vertex hvertex i)

end EditApproximation

end OAI
