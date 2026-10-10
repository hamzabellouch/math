import OAI.Geometry.RCD.Coordinates.PositiveBilinearMeasure

namespace OAI

/-! # The actual scaled Bochner masses and their Gaussian envelope -/

open Set Metric MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The full positive Bochner measure on a fixed-root dyadic ball, with
the dimensional scaling used by the heat decrement. -/
def dyadicBochnerMass (M : PositiveBilinearMeasure X E) (n : ℕ)
    (p : X) (R : ℝ) (i : ℕ) : E →L[ℝ] E :=
  ((R / 2 ^ i) ^ 2 / (R / 2 ^ i) ^ n) • M.massOperator (ball p (R / 2 ^ i))

theorem dyadicBochnerMass_isPositive (M : PositiveBilinearMeasure X E) (n : ℕ)
    (p : X) {R : ℝ} (hR : 0 ≤ R) (i : ℕ) :
    (dyadicBochnerMass M n p R i).IsPositive := by
  apply (M.massOperator_isPositive _ measurableSet_ball).smul_of_nonneg
  exact div_nonneg (sq_nonneg _) (pow_nonneg (div_nonneg hR (by positivity)) _)

theorem dyadicBochnerMass_inner (M : PositiveBilinearMeasure X E) (n : ℕ)
    (p : X) (R : ℝ) (i : ℕ) (v : E) :
    ⟪v, dyadicBochnerMass M n p R i v⟫_ℝ =
      ((R / 2 ^ i) ^ 2 / (R / 2 ^ i) ^ n) * (M.measure v).real (ball p (R / 2 ^ i)) := by
  simp only [dyadicBochnerMass, smul_apply, inner_smul_right,
    M.measure_real v _ measurableSet_ball]

omit [MetricSpace X] [BorelSpace X] in
/-- The fixed finite source has a single operator-norm bound for its total
mass in every direction. No absolute continuity is required. -/
theorem bochner_total_mass_le (M : PositiveBilinearMeasure X E) (v : E) :
    (M.measure v).real univ ≤ ‖M.massOperator univ‖ * ‖v‖ ^ 2 := by
  rw [M.measure_real v univ MeasurableSet.univ]
  calc
    _ ≤ ‖v‖ * ‖M.massOperator univ v‖ := real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖M.massOperator univ‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left ((M.massOperator univ).le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

/-- The actual positive mass envelope used in the cumulative comparison. -/
def dyadicBochnerEnvelope (M : PositiveBilinearMeasure X E) (n : ℕ)
    (p : X) (R : ℝ) (i : ℕ) : E →L[ℝ] E :=
  (3 / 4 : ℝ) ^ i • ContinuousLinearMap.id ℝ E +
    ∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ (i - j) • dyadicBochnerMass M n p R j

theorem dyadicBochnerEnvelope_isPositive (M : PositiveBilinearMeasure X E) (n : ℕ)
    (p : X) {R : ℝ} (hR : 0 ≤ R) (i : ℕ) :
    (dyadicBochnerEnvelope M n p R i).IsPositive := by
  apply ContinuousLinearMap.IsPositive.add
  · exact ContinuousLinearMap.isPositive_id.smul_of_nonneg (by positivity)
  · apply ContinuousLinearMap.isPositive_sum
    intro j _
    exact (dyadicBochnerMass_isPositive M n p hR j).smul_of_nonneg (by positivity)

omit [BorelSpace X] in
theorem dyadicBochnerEnvelope_inner (M : PositiveBilinearMeasure X E) (n : ℕ)
    (p : X) (R : ℝ) (i : ℕ) (v : E) :
    ⟪v, dyadicBochnerEnvelope M n p R i v⟫_ℝ =
      (3 / 4 : ℝ) ^ i * ‖v‖ ^ 2 +
        ∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ (i - j) *
          ⟪v, dyadicBochnerMass M n p R j v⟫_ℝ := by
  simp only [dyadicBochnerEnvelope, add_apply,
    smul_apply, ContinuousLinearMap.id_apply,
    sum_apply, inner_add_right, inner_smul_right,
    inner_sum, real_inner_self_eq_norm_sq]

end RegularPointCoordinates

end

end OAI
