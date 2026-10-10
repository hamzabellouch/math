import OAI.Geometry.RCD.Coordinates.OpenCoordinates
import OAI.Geometry.RCD.Coordinates.MetricIteration

namespace OAI

/-! # The quarter-scale open-map construction supplies dyadic ellipsoids -/

open Set

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [CompleteSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coordinateQuarterRadius_eq_even_iterationRadius (r : ℝ) (i : ℕ) :
    coordinateQuarterRadius r i = iterationRadius r (2 * i) := by
  simp only [coordinateQuarterRadius, iterationRadius, pow_mul]
  rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
  rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow, div_eq_mul_inv]

theorem quarter_half_index_bounds {r : ℝ} (hr : 0 ≤ r) (i : ℕ) :
    iterationRadius r i ≤ coordinateQuarterRadius r (i / 2) ∧
      coordinateQuarterRadius r (i / 2) ≤ 2 * iterationRadius r i := by
  have hi : i = 2 * (i / 2) + i % 2 := by omega
  rcases Nat.mod_two_eq_zero_or_one i with hm | hm
  · have he : i = 2 * (i / 2) := by omega
    rw [coordinateQuarterRadius_eq_even_iterationRadius, ← he]
    have hn : 0 ≤ iterationRadius r i := div_nonneg hr (pow_nonneg (by norm_num) i)
    constructor <;> linarith
  · have he : iterationRadius r i = coordinateQuarterRadius r (i / 2) / 2 := by
      conv_lhs => rw [hi, hm]
      rw [coordinateQuarterRadius_eq_even_iterationRadius]
      simp only [iterationRadius, pow_succ]
      ring
    rw [he]
    have hn : 0 ≤ coordinateQuarterRadius r (i / 2) :=
      mul_nonneg hr (pow_nonneg (by norm_num) _)
    constructor <;> linarith

/-- Comparable normalizations transfer the exact preimages to a desired
frozen ellipsoid. The dyadic radius may lie between consecutive quarter
scales. -/
theorem ellipsoid_preimages_of_comparable_normalizations
    {Ω : Set X} {f : X → E} {r C ρ : ℝ}
    (d : OpenCoordinateData Ω f r C) (hr : 0 < r) (hC : 0 ≤ C)
    (hcont : ContinuousOn f Ω) (j : ℕ) (x : X) (T : E ≃L[ℝ] E)
    (hρ : 0 < ρ)
    (hlower : ρ ≤ coordinateQuarterRadius r j)
    (hupper : coordinateQuarterRadius r j ≤ 2 * ρ)
    (hball : Metric.ball x (2 * coordinateQuarterRadius r j) ⊆ Ω)
    (hcompare : ∀ w, ‖d.normalization j x w‖ ≤ 2 * ‖T w‖) :
    ∀ P : E, ‖T (P - f x)‖ < ρ / 32 →
      ∃ y ∈ Ω, dist x y < ρ ∧ f y = P := by
  intro P hP
  have hnorm : ‖d.normalization j x (P - f x)‖ <
      coordinateQuarterRadius r j / 16 := by
    have hc := hcompare (P - f x)
    linarith
  obtain ⟨y, hy, heq⟩ := d.exists_preimage hr hC hcont j x hball hnorm
  have hR : 0 < coordinateQuarterRadius r j :=
    mul_pos hr (pow_pos (by norm_num) j)
  refine ⟨y, hball ?_, ?_, heq⟩
  · change dist y x < 2 * coordinateQuarterRadius r j
    linarith
  · rw [dist_comm]
    linarith

/-- Even dyadic scales are exactly the quarter scales used in the Cauchy
correction argument. This version has no scale-comparability premise. -/
theorem even_iteration_ellipsoid_preimages
    {Ω : Set X} {f : X → E} {r C : ℝ}
    (d : OpenCoordinateData Ω f r C) (hr : 0 < r) (hC : 0 ≤ C)
    (hcont : ContinuousOn f Ω) (j : ℕ) (x : X) (T : E ≃L[ℝ] E)
    (hball : Metric.ball x (2 * iterationRadius r (2 * j)) ⊆ Ω)
    (hcompare : ∀ w, ‖d.normalization j x w‖ ≤ 2 * ‖T w‖) :
    ∀ P : E, ‖T (P - f x)‖ < iterationRadius r (2 * j) / 32 →
      ∃ y ∈ Ω, dist x y < iterationRadius r (2 * j) ∧ f y = P := by
  have heq := coordinateQuarterRadius_eq_even_iterationRadius r j
  apply ellipsoid_preimages_of_comparable_normalizations d hr hC hcont j x T
  · rw [← heq]
    exact mul_pos hr (pow_pos (by norm_num) j)
  · exact heq.ge
  · rw [← heq]
    have hpos : 0 < coordinateQuarterRadius r j :=
      mul_pos hr (pow_pos (by norm_num) j)
    linarith
  · simpa only [heq] using hball
  · exact hcompare

/-- The working ball of radius `4 r_i` suffices for every dyadic index,
including the odd indices between successive quarter scales. -/
theorem dyadic_ellipsoid_preimages
    {Ω : Set X} {f : X → E} {r C : ℝ}
    (d : OpenCoordinateData Ω f r C) (hr : 0 < r) (hC : 0 ≤ C)
    (hcont : ContinuousOn f Ω) (i : ℕ) (x : X) (T : E ≃L[ℝ] E)
    (hball : Metric.ball x (4 * iterationRadius r i) ⊆ Ω)
    (hcompare : ∀ w, ‖d.normalization (i / 2) x w‖ ≤ 2 * ‖T w‖) :
    ∀ P : E, ‖T (P - f x)‖ < iterationRadius r i / 32 →
      ∃ y ∈ Ω, dist x y < iterationRadius r i ∧ f y = P := by
  obtain ⟨hl, hu⟩ := quarter_half_index_bounds hr.le i
  apply ellipsoid_preimages_of_comparable_normalizations d hr hC hcont
    (i / 2) x T (div_pos hr (pow_pos (by norm_num) i)) hl hu
  · intro y hy
    apply hball
    have hy' : dist y x < 2 * coordinateQuarterRadius r (i / 2) := hy
    change dist y x < 4 * iterationRadius r i
    linarith
  · exact hcompare

end RegularPointCoordinates

end OAI
