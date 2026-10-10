import OAI.Combinatorics.EditApproximation.Numerics.VectorOptimizerWork

namespace OAI

/-! Representation bounds for the actual stored optimizer iterates. -/

namespace EditApproximation

open Finset

theorem finiteRationalOptimizer_coordinate_bounds {ι : Type*}
    (coordinates : Finset ι) (vertices : List (ι → ℚ)) (linear : ι → ℚ)
    (G j : ℕ) (hvertices : vertices ≠ []) (i : ι)
    (hinput : ∀ vertex ∈ vertices, 0 ≤ vertex i ∧ vertex i ≤ 1) :
    0 ≤ finiteRationalOptimizer coordinates vertices linear G j i ∧
      finiteRationalOptimizer coordinates vertices linear G j i ≤ 1 := by
  induction j with
  | zero =>
    cases vertices with
    | nil => exact False.elim (hvertices rfl)
    | cons vertex rest => exact hinput vertex List.mem_cons_self
  | succ j ih =>
    have hselected := (rationalLinearizationMaximizer_spec coordinates vertices
      (rationalSmoothedGradient G linear (finiteRationalOptimizer coordinates vertices linear G j))
      hvertices).1
    have hbounds := hinput _ hselected
    have hden : (0 : ℚ) < (j : ℚ) + 2 := by positivity
    have hweight : (0 : ℚ) ≤ 2 / ((j : ℚ) + 2) := by positivity
    have hweightOne : (2 : ℚ) / ((j : ℚ) + 2) ≤ 1 :=
      (div_le_one₀ hden).2 (by have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg _; linarith)
    change 0 ≤ (1 - 2 / ((j : ℚ) + 2)) * _ + 2 / ((j : ℚ) + 2) * _ ∧
      (1 - 2 / ((j : ℚ) + 2)) * _ + 2 / ((j : ℚ) + 2) * _ ≤ 1
    have hcomplement : 0 ≤ 1 - (2 : ℚ) / ((j : ℚ) + 2) := sub_nonneg.mpr hweightOne
    constructor
    · exact add_nonneg (mul_nonneg hcomplement ih.1) (mul_nonneg hweight hbounds.1)
    · calc
        _ ≤ (1 - 2 / ((j : ℚ) + 2)) * 1 + (2 : ℚ) / ((j : ℚ) + 2) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left ih.2 hcomplement)
            (mul_le_mul_of_nonneg_left hbounds.2 hweight)
        _ = 1 := by ring

theorem materializedOptimizerWithWork_denominator {d : ℕ}
    (vertices : List (Vector ℚ d)) (linear : Vector ℚ d) (G K B : ℕ)
    (hvertices : vertices ≠ []) (hK : 0 < K) (i : Fin d)
    (hinput : ∀ vertex ∈ vertices, Nat.size (vertex.get i).den ≤ B) :
    Nat.size ((materializedOptimizerWithWork vertices linear G K).1.get i).den ≤
      K * (2 * Nat.size K + 2 + B) + 1 := by
  rw [materializedOptimizerWithWork_value, finiteRationalOptimizer_eq_iterate]
  apply rationalOptimizerIterate_denominator_bit_length _ _ K B hK i
  intro j _
  have hlist : vertices.map Vector.get ≠ [] := by
    intro hempty
    exact hvertices (List.map_eq_nil_iff.mp hempty)
  have hmember := (rationalLinearizationMaximizer_spec univ (vertices.map Vector.get)
    (rationalSmoothedGradient G linear.get
      (finiteRationalOptimizer univ (vertices.map Vector.get) linear.get G j)) hlist).1
  obtain ⟨vertex, hv, heq⟩ := List.mem_map.mp hmember
  change Nat.size (finiteOptimizerSelection univ (vertices.map Vector.get) linear.get G j i).den ≤ B
  unfold finiteOptimizerSelection
  rw [← heq]
  exact hinput vertex hv

theorem materializedOptimizerWithWork_encoding {d : ℕ}
    (vertices : List (Vector ℚ d)) (linear : Vector ℚ d) (G K B : ℕ)
    (hvertices : vertices ≠ []) (hK : 0 < K) (i : Fin d)
    (hinput : ∀ vertex ∈ vertices,
      (0 ≤ vertex.get i ∧ vertex.get i ≤ 1) ∧ Nat.size (vertex.get i).den ≤ B) :
    rationalEncodingBits ((materializedOptimizerWithWork vertices linear G K).1.get i) ≤
      2 * (K * (2 * Nat.size K + 2 + B) + 1) + 1 := by
  have hlist : vertices.map Vector.get ≠ [] := by
    intro hempty
    exact hvertices (List.map_eq_nil_iff.mp hempty)
  have hpoint := finiteRationalOptimizer_coordinate_bounds univ (vertices.map Vector.get)
    linear.get G K hlist i (by
      intro vertex hv
      obtain ⟨stored, hs, rfl⟩ := List.mem_map.mp hv
      exact (hinput stored hs).1)
  rw [← materializedOptimizerWithWork_value vertices linear G K] at hpoint
  have habs : |(materializedOptimizerWithWork vertices linear G K).1.get i| ≤ 1 := by
    rw [abs_of_nonneg hpoint.1]
    exact hpoint.2
  have hnum := Nat.size_le_size (rational_numerator_bound _ 1 habs)
  simp only [Nat.one_mul] at hnum
  have hden := materializedOptimizerWithWork_denominator vertices linear G K B hvertices hK i
    (fun vertex hv => (hinput vertex hv).2)
  unfold rationalEncodingBits
  omega

end EditApproximation

end OAI
