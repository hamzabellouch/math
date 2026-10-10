import OAI.Combinatorics.EditApproximation.Geometry.OnlineActionDraw
import OAI.Combinatorics.EditApproximation.Geometry.ChildIncrements
import OAI.Combinatorics.EditApproximation.Probability.SampledRegret

namespace OAI

/-!
# Regret and sampling for the literal finite band list

The numerical optimizer and exact sampler keep the same listed vertex
order. Passing to the finite set is used only for coordinate support and
convex-hull facts, never to reorder the executable optimizer.
-/

namespace EditApproximation

open Finset

theorem rationalVertexSet_band_list {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (mass : β → ℚ) :
    rationalVertexSet (band.map (actionVector mass)) =
      rationalVertexSet (band.toFinset.toList.map (actionVector mass)) := by
  unfold rationalVertexSet
  congr 1
  ext vertex
  simp only [Set.mem_ofPred_eq, List.mem_map, mem_toList, List.mem_toFinset]

/-- Actual finite-list specialization of the computed entropy optimizer. -/
theorem list_band_computed_entropy_regret {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : List (β → σ)) (hband : band ≠ [])
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child)
    (S H : ℕ) (η κ : ℚ) (rangeBound : ℝ)
    (gain decrement : ℕ → β × σ → ℚ) {comparison : β → σ} (hc : comparison ∈ band)
    (hH : 4 ≤ H) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : (η : ℝ) * rangeBound ≤ (κ : ℝ))
    (hdecrementNonneg : ∀ t < S, ∀ i ∈ bandCoordinates band.toFinset, (0 : ℝ) ≤ decrement t i)
    (hrange : ∀ t < S, ∀ i ∈ bandCoordinates band.toFinset, ∀ j ∈ bandCoordinates band.toFinset,
      i.1 = j.1 → |(decrement t i : ℝ) - decrement t j| ≤ rangeBound)
    (hdecrement : ∀ i ∈ bandCoordinates band.toFinset, ∑ t ∈ range S, (decrement t i : ℝ) ≤ 1)
    (hgain : ∀ t < S, ∀ i ∈ bandCoordinates band.toFinset,
      -1 ≤ (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i ∧
        (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i ≤ 0) :
    (∑ t ∈ range S, ∑ i ∈ bandCoordinates band.toFinset,
        ((gain t i : ℝ) + decrement t i) * (actionVector mass comparison i : ℝ)) -
        Real.log (bandCoordinates band.toFinset).card / (η : ℝ) - 2 * (κ : ℝ) - (S : ℝ) / (H : ℝ) ^ 3 ≤
      ∑ t ∈ range S, ∑ i ∈ bandCoordinates band.toFinset,
        ((gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i) *
          (computedOnlineVector (bandCoordinates band.toFinset) (band.map (actionVector mass))
            η κ gain decrement H t i : ℝ) := by
  have hvertices : band.map (actionVector mass) ≠ [] := by
    cases band with
    | nil => exact False.elim (hband rfl)
    | cons action rest => simp
  have hcSet : comparison ∈ band.toFinset := List.mem_toFinset.mpr hc
  have hset := rationalVertexSet_band_list band mass
  apply computed_finite_block_entropy_regret (bandCoordinates band.toFinset) Prod.fst
    (band.map (actionVector mass)) S H η κ rangeBound gain decrement
    (fun i => (actionVector mass comparison i : ℝ)) hvertices hH
  · intro p hp
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hp
    exact actionVector_probability band.toFinset mass hpos (List.mem_toFinset.mpr ha)
  · intro i hi
    obtain ⟨action, ha, hpositive⟩ := actionVector_coordinate_coverage band.toFinset mass hpos i hi
    exact ⟨actionVector mass action, List.mem_map.mpr ⟨action, List.mem_toFinset.mp ha, rfl⟩, hpositive⟩
  · exact subset_convexHull ℝ _ ⟨actionVector mass comparison, List.mem_map.mpr ⟨comparison, hc, rfl⟩, rfl⟩
  · exact band_block_nonempty band.toFinset ⟨comparison, hcSet⟩
  · intro p hp q hq b
    rw [hset] at hp hq
    rw [band_hull_block_mass band.toFinset mass b p hp, band_hull_block_mass band.toFinset mass b q hq]
  · exact hη
  · exact hκ
  · exact hκhalf
  · exact hηrange
  · exact hdecrementNonneg
  · exact hrange
  · exact hdecrement
  · exact hgain

theorem finiteOptimizerActionDraw_linear_mean {β σ : Type*} [Fintype β]
    [DecidableEq β] [DecidableEq σ] (band : List (β → σ)) (hband : band ≠ [])
    (mass : β → ℚ) (linear : β × σ → ℚ) (G K : ℕ) (hK : 0 < K)
    (payoff : β × σ → ℝ) :
    uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
      ∑ coordinate ∈ bandCoordinates band.toFinset,
        payoff coordinate * (actionVector mass
          (finiteOptimizerActionDraw band hband mass linear G K integer) coordinate : ℝ)) =
      ∑ coordinate ∈ bandCoordinates band.toFinset,
        payoff coordinate * (finiteRationalOptimizer (bandCoordinates band.toFinset)
          (band.map (actionVector mass)) linear G K coordinate : ℝ) := by
  unfold uniformMean
  rw [Fintype.card_fin, sum_comm, sum_div]
  apply sum_congr rfl
  intro coordinate hc
  rw [← mul_sum, mul_div_assoc]
  congr 1
  exact_mod_cast finiteOptimizerActionDraw_mean band hband mass linear G K hK coordinate

/-- Exact expected weighted child cost of the returned optimizer action. -/
theorem finiteOptimizerActionDraw_child_cost_mean {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : List (β → σ)) (hband : band ≠ [])
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child)
    (table : ℕ → β × σ → ℚ) (κ : ℚ) (t : ℕ)
    (linear : β × σ → ℚ) (G K : ℕ) (hK : 0 < K) :
    uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
      let action := finiteOptimizerActionDraw band hband mass linear G K integer
      (∑ child, (table (t + 1) (child, action child) : ℝ)) +
        (κ : ℝ) * ((∑ child, (table t (child, action child) : ℝ)) -
          ∑ child, (table (t + 1) (child, action child) : ℝ))) =
      -((∑ child, mass child : ℚ) : ℝ) *
        ∑ coordinate ∈ bandCoordinates band.toFinset,
          ((childGain mass table t coordinate : ℝ) + (1 - (κ : ℝ)) * childDecrement mass table t coordinate) *
            (finiteRationalOptimizer (bandCoordinates band.toFinset)
              (band.map (actionVector mass)) linear G K coordinate : ℝ) := by
  have hpoint (integer : Fin (optimizerTriangularMass K)) := actionVector_child_cost_identity
    band.toFinset mass hpos table κ t (List.mem_toFinset.mpr
      (finiteOptimizerActionDraw_mem band hband mass linear G K integer))
  simp_rw [← hpoint]
  rw [uniformMean_mul, finiteOptimizerActionDraw_linear_mean band hband mass linear G K hK]

end EditApproximation

end OAI
