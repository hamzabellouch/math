import OAI.Geometry.RCD.Coordinates.RegularFrozenMass

namespace OAI

/-! # Envelopes for the actual full mass of nearby patches -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The raw full mass before conjugation by the patch's mean. -/
def rawPinchingMass (M : PositiveBilinearMeasure X E) (n : ℕ)
    (R : ℝ) (z : X) (i : ℕ) : E →L[ℝ] E :=
  let s := distanceSourceRadius R i
  (s ^ 2 / s ^ n) • M.massOperator (ball z (s / 49152))

/-- The scaling ratio from the source radius to the enclosing dyadic mass. -/
def patchEnvelopeFactor (n : ℕ) : ℝ :=
  (4 / 3 : ℝ) * ((32768 : ℝ) ^ 2 / (32768 : ℝ) ^ n)

/-- A patch lying within one twelfth of the mean radius is contained in
the preceding central dyadic mass ball, a term of the actual heat envelope. -/
theorem rawPinchingMass_le_envelope (M : PositiveBilinearMeasure X E) (n : ℕ)
    {R : ℝ} (hR : 0 < R) {q z : X} (i : ℕ)
    (hroom : dist z q ≤ (R / (2 : ℝ) ^ (i + 15)) / 12) (v : E) :
    ⟪v, rawPinchingMass M n R z i v⟫_ℝ ≤
      patchEnvelopeFactor n * ⟪v, dyadicBochnerEnvelope M n q R (i + 17) v⟫_ℝ := by
  let r := R / (2 : ℝ) ^ (i + 16)
  let s := distanceSourceRadius R i
  have hr : 0 < r := div_pos hR (by positivity)
  have hs : s = 32768 * r := by
    dsimp only [r, s, distanceSourceRadius]
    rw [show i + 16 = (i + 1) + 15 by omega, pow_add]
    norm_num
    ring
  have hrmean : R / (2 : ℝ) ^ (i + 15) = 2 * r := by
    dsimp only [r]
    rw [show i + 16 = (i + 15) + 1 by omega, pow_add]
    norm_num
    ring
  have hball : ball z (s / 49152) ⊆ ball q r := by
    apply ball_subset_ball'
    rw [hrmean] at hroom
    rw [hs]
    linarith
  have hmass := measureReal_mono (μ := M.measure v) hball (measure_ne_top _ _)
  rw [M.measure_real v _ measurableSet_ball, M.measure_real v _ measurableSet_ball] at hmass
  have hscale : s ^ 2 / s ^ n = ((32768 : ℝ) ^ 2 / (32768 : ℝ) ^ n) * (r ^ 2 / r ^ n) := by
    rw [hs, mul_pow, mul_pow]
    ring
  have hraw : ⟪v, rawPinchingMass M n R z i v⟫_ℝ ≤
      ((32768 : ℝ) ^ 2 / (32768 : ℝ) ^ n) * ⟪v, dyadicBochnerMass M n q R (i + 16) v⟫_ℝ := by
    change ⟪v, ((s ^ 2 / s ^ n) • M.massOperator (ball z (s / 49152))) v⟫_ℝ ≤ _
    rw [smul_apply, inner_smul_right, hscale]
    change _ ≤ ((32768 : ℝ) ^ 2 / (32768 : ℝ) ^ n) *
      ⟪v, ((r ^ 2 / r ^ n) • M.massOperator (ball q r)) v⟫_ℝ
    rw [smul_apply, inner_smul_right]
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass
      (show 0 ≤ r ^ 2 / r ^ n by positivity))
      (show 0 ≤ (32768 : ℝ) ^ 2 / (32768 : ℝ) ^ n by positivity)
    convert h using 1
    ring
  have hterm : (3 / 4 : ℝ) * ⟪v, dyadicBochnerMass M n q R (i + 16) v⟫_ℝ ≤
      ⟪v, dyadicBochnerEnvelope M n q R (i + 17) v⟫_ℝ := by
    rw [dyadicBochnerEnvelope_inner]
    have h := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.range (i + 17 + 1)) =>
        mul_nonneg (by positivity : 0 ≤ (3 / 4 : ℝ) ^ (i + 17 - j))
          ((dyadicBochnerMass_isPositive M n q hR.le j).inner_nonneg_right v))
      (show i + 16 ∈ Finset.range (i + 17 + 1) by simp)
    rw [show i + 17 - (i + 16) = 1 by omega, pow_one] at h
    exact h.trans (le_add_of_nonneg_left (by positivity))
  have hm := mul_le_mul_of_nonneg_left hterm
    (show 0 ≤ (4 / 3 : ℝ) * ((32768 : ℝ) ^ 2 / (32768 : ℝ) ^ n) by positivity)
  dsimp only [patchEnvelopeFactor]
  exact hraw.trans (by nlinarith only [hm])

end RegularPointCoordinates

end

end OAI
