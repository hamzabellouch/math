import OAI.Combinatorics.EditApproximation.Geometry.ActionVectors
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Regret of the computed rational band mixtures

The optimistic objective is computed in rational arithmetic. The finite
optimizer supplies every predicted vector used here; no maximization
oracle or unproved entropy-regret hypothesis appears in the conclusion.
-/

namespace EditApproximation

open Finset



theorem rationalOptimisticHistory_cast {ι : Type*} (κ : ℚ)
    (gain decrement : ℕ → ι → ℚ) (t : ℕ) (i : ι) :
    (rationalOptimisticHistory κ gain decrement t i : ℝ) =
      optimisticHistory (κ : ℝ) (fun j i => (gain j i : ℝ))
        (fun j i => (decrement j i : ℝ)) t i := by
  simp [rationalOptimisticHistory, optimisticHistory]



def computedOnlineVector {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (η κ : ℚ)
    (gain decrement : ℕ → ι → ℚ) (H t : ℕ) : ι → ℚ :=
  finiteRationalOptimizer coordinates vertices (rationalOnlineLinear η κ gain decrement t)
    (H + coordinates.card + 2) ((H + coordinates.card + 2) ^ 80)

theorem rationalOnlineLinear_objective {ι : Type*} (coordinates : Finset ι)
    (η κ : ℚ) (gain decrement : ℕ → ι → ℚ) (t : ℕ) (p : ι → ℝ) :
    entropyValue coordinates 1
        (fun i => (rationalOnlineLinear η κ gain decrement t i : ℝ)) p =
      entropyValue coordinates (η : ℝ)
        (fun i => optimisticHistory (κ : ℝ) (fun j i => (gain j i : ℝ))
          (fun j i => (decrement j i : ℝ)) t i + (gain t i : ℝ)) p := by
  unfold entropyValue
  apply sum_congr rfl
  intro i _
  simp only [rationalOnlineLinear, Rat.cast_mul, Rat.cast_add,
    rationalOptimisticHistory_cast, one_mul]

/-- Fixed-block regret for the actual rational optimizer, with its
prescribed `G^80` iterations and `H^-3` numerical loss. -/
theorem computed_finite_block_entropy_regret {ι β : Type*} [Fintype β] [DecidableEq β]
    (coordinates : Finset ι) (block : ι → β) (vertices : List (ι → ℚ))
    (S H : ℕ) (η κ : ℚ) (rangeBound : ℝ)
    (gain decrement : ℕ → ι → ℚ) (comparator : ι → ℝ)
    (hvertices : vertices ≠ []) (hH : 4 ≤ H)
    (hprobability : ∀ p ∈ vertices,
      (∀ i ∈ coordinates, (0 : ℝ) ≤ p i) ∧ (∑ i ∈ coordinates, (p i : ℝ)) = 1)
    (hcovered : ∀ i ∈ coordinates, ∃ p ∈ vertices, (0 : ℝ) < p i)
    (hcQ : comparator ∈ convexHull ℝ (rationalVertexSet vertices))
    (hblocks : ∀ b, (coordinates.filter (fun i => block i = b)).Nonempty)
    (hblockMass : ∀ p ∈ convexHull ℝ (rationalVertexSet vertices),
      ∀ q ∈ convexHull ℝ (rationalVertexSet vertices), ∀ b,
      (∑ i ∈ coordinates with block i = b, p i) =
        ∑ i ∈ coordinates with block i = b, q i)
    (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : (η : ℝ) * rangeBound ≤ (κ : ℝ))
    (hdecrementNonneg : ∀ t < S, ∀ i ∈ coordinates, (0 : ℝ) ≤ decrement t i)
    (hrange : ∀ t < S, ∀ i ∈ coordinates, ∀ j ∈ coordinates,
      block i = block j → |(decrement t i : ℝ) - decrement t j| ≤ rangeBound)
    (hdecrement : ∀ i ∈ coordinates, ∑ t ∈ range S, (decrement t i : ℝ) ≤ 1)
    (hgain : ∀ t < S, ∀ i ∈ coordinates,
      -1 ≤ (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i ∧
        (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i ≤ 0) :
    (∑ t ∈ range S, ∑ i ∈ coordinates,
        ((gain t i : ℝ) + decrement t i) * comparator i) -
        Real.log coordinates.card / (η : ℝ) - 2 * (κ : ℝ) - (S : ℝ) / (H : ℝ) ^ 3 ≤
      ∑ t ∈ range S, ∑ i ∈ coordinates,
        ((gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i) *
          (computedOnlineVector coordinates vertices η κ gain decrement H t i : ℝ) := by
  classical
  have hfinite : ({p : ι → ℚ | p ∈ vertices} : Set (ι → ℚ)).Finite := by simp
  have hcompact := (hfinite.image (fun p : ι → ℚ => fun i => (p i : ℝ))).isCompact_convexHull ℝ
  obtain ⟨witness, hwQ, hw⟩ := rationalVertexHull_positive_witness coordinates vertices
    hvertices (fun p hp => (hprobability p hp).1) hcovered
  have hoptimizer (t : ℕ) := finite_entropy_optimizer coordinates vertices
    (rationalOnlineLinear η κ gain decrement t) H hvertices hH hprobability hcovered
  choose predicted hpred using hoptimizer
  have hpredMax t : IsMaxOn
      (entropyValue coordinates (η : ℝ)
        (fun i => optimisticHistory (κ : ℝ) (fun j i => (gain j i : ℝ))
          (fun j i => (decrement j i : ℝ)) t i + (gain t i : ℝ)))
      (convexHull ℝ (rationalVertexSet vertices)) (predicted t) := by
    intro q hq
    have hbound := (hpred t).2.1 hq
    change entropyValue coordinates 1
        (fun i => (rationalOnlineLinear η κ gain decrement t i : ℝ)) q ≤
      entropyValue coordinates 1
        (fun i => (rationalOnlineLinear η κ gain decrement t i : ℝ)) (predicted t) at hbound
    rw [rationalOnlineLinear_objective, rationalOnlineLinear_objective] at hbound
    exact hbound
  have hκhalfR : (κ : ℝ) ≤ 1 / 2 := by
    calc
      (κ : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hκhalf
      _ = 1 / 2 := by norm_num
  have hregret := finite_block_entropy_regret coordinates block
    (convexHull ℝ (rationalVertexSet vertices)) S (η : ℝ) (κ : ℝ) rangeBound
    (fun j i => (gain j i : ℝ)) (fun j i => (decrement j i : ℝ)) predicted
    witness comparator hcompact (convex_convexHull ℝ _) hwQ hcQ hw
    (rationalVertexHull_probability coordinates vertices hprobability) hblocks hblockMass
    (by exact_mod_cast hη) (by exact_mod_cast hκ) hκhalfR hηrange
    (fun t _ => (hpred t).1) (fun t _ => hpredMax t)
    hdecrementNonneg hrange hdecrement
  have hloss := sum_le_sum fun t (ht : t ∈ range S) =>
    bounded_gain_l1_approximation coordinates
      (fun i => (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i)
      (predicted t) (fun i => (computedOnlineVector coordinates vertices η κ gain decrement H t i : ℝ))
      (1 / (H : ℝ) ^ 3) (hgain t (mem_range.mp ht)) (hpred t).2.2
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at hloss
  rw [mul_one_div] at hloss
  linarith

/-- Specialization to the actual child/state coordinates and rational
fixed child masses of a nonempty band. -/
theorem band_computed_entropy_regret {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : Finset (β → σ)) (hband : band.Nonempty)
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child)
    (S H : ℕ) (η κ : ℚ) (rangeBound : ℝ)
    (gain decrement : ℕ → β × σ → ℚ) {comparison : β → σ} (hc : comparison ∈ band)
    (hH : 4 ≤ H) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : (η : ℝ) * rangeBound ≤ (κ : ℝ))
    (hdecrementNonneg : ∀ t < S, ∀ i ∈ bandCoordinates band, (0 : ℝ) ≤ decrement t i)
    (hrange : ∀ t < S, ∀ i ∈ bandCoordinates band, ∀ j ∈ bandCoordinates band,
      i.1 = j.1 → |(decrement t i : ℝ) - decrement t j| ≤ rangeBound)
    (hdecrement : ∀ i ∈ bandCoordinates band, ∑ t ∈ range S, (decrement t i : ℝ) ≤ 1)
    (hgain : ∀ t < S, ∀ i ∈ bandCoordinates band,
      -1 ≤ (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i ∧
        (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i ≤ 0) :
    (∑ t ∈ range S, ∑ i ∈ bandCoordinates band,
        ((gain t i : ℝ) + decrement t i) * (actionVector mass comparison i : ℝ)) -
        Real.log (bandCoordinates band).card / (η : ℝ) - 2 * (κ : ℝ) - (S : ℝ) / (H : ℝ) ^ 3 ≤
      ∑ t ∈ range S, ∑ i ∈ bandCoordinates band,
        ((gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i) *
          (computedOnlineVector (bandCoordinates band) (band.toList.map (actionVector mass))
            η κ gain decrement H t i : ℝ) := by
  have hvertices : band.toList.map (actionVector mass) ≠ [] := by
    intro hnil
    have hmem : actionVector mass comparison ∈ band.toList.map (actionVector mass) :=
      List.mem_map.mpr ⟨comparison, mem_toList.mpr hc, rfl⟩
    simp only [hnil, List.not_mem_nil] at hmem
  apply computed_finite_block_entropy_regret (bandCoordinates band) Prod.fst
    (band.toList.map (actionVector mass)) S H η κ rangeBound gain decrement
    (fun i => (actionVector mass comparison i : ℝ)) hvertices hH
  · intro p hp
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hp
    exact actionVector_probability band mass hpos (mem_toList.mp ha)
  · intro i hi
    obtain ⟨action, ha, hpositive⟩ := actionVector_coordinate_coverage band mass hpos i hi
    exact ⟨actionVector mass action, List.mem_map.mpr ⟨action, mem_toList.mpr ha, rfl⟩, hpositive⟩
  · exact subset_convexHull ℝ _ ⟨actionVector mass comparison,
      List.mem_map.mpr ⟨comparison, mem_toList.mpr hc, rfl⟩, rfl⟩
  · exact band_block_nonempty band hband
  · intro p hp q hq b
    rw [band_hull_block_mass band mass b p hp, band_hull_block_mass band mass b q hq]
  · exact hη
  · exact hκ
  · exact hκhalf
  · exact hηrange
  · exact hdecrementNonneg
  · exact hrange
  · exact hdecrement
  · exact hgain

end EditApproximation

end OAI
