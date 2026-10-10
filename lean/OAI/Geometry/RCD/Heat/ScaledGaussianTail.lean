import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.GaussianVolumeTail

namespace OAI

/-! # Off-diagonal decay at a fixed relative scale -/

open Set Metric MeasureTheory Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

private theorem inverse_power_sqrt (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (t⁻¹) ^ ((n : ℝ) / 2) = ((Real.sqrt t) ^ n)⁻¹ := by
  have hs : (Real.sqrt t) ^ n = t ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht.le]
    congr 1
    ring
  rw [Real.inv_rpow ht.le, hs]

private theorem gaussian_envelope_scale (n : ℕ) {R t c D b : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (ht : 0 < t) (hb : 0 ≤ b) :
    R ^ n * gaussianOffDiagonalEnvelope ((n : ℝ) / 2) ((c * R) ^ 2 / D) b t ≤
      gaussianOffDiagonalEnvelope ((n : ℝ) / 2) (c ^ 2 / D) b (t / R ^ 2) := by
  have hτ : 0 < t / R ^ 2 := div_pos ht (sq_pos_of_pos hR)
  have hfactor : R ^ n * ((Real.sqrt t) ^ n)⁻¹ =
      ((Real.sqrt (t / R ^ 2)) ^ n)⁻¹ := by
    rw [Real.sqrt_div ht.le, Real.sqrt_sq hR.le, div_pow, inv_div]
    ring
  have hexponent : -((c * R) ^ 2 / D) * t⁻¹ =
      -(c ^ 2 / D) * (t / R ^ 2)⁻¹ := by
    simp only [mul_pow, div_eq_mul_inv, inv_inv, mul_inv_rev]
    ring
  have htime : t ≤ t / R ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    exact mul_le_of_le_one_right ht.le (by nlinarith)
  unfold gaussianOffDiagonalEnvelope
  rw [inverse_power_sqrt n ht, inverse_power_sqrt n hτ, ← mul_assoc, hfactor]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) _))
  apply Real.exp_le_exp.mpr
  rw [hexponent]
  linarith [mul_le_mul_of_nonneg_left htime hb]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (ker : ℝ → X → X → ℝ)

/-- The small relative time is chosen before the physical radius. -/
theorem HasCoordinateHeatBounds.scaled_off_diagonal_small
    (hg : HasCoordinateHeatBounds μ ker)
    (hnonneg : ∀ t, 0 < t → ∀ x y, 0 ≤ ker t x y)
    (n : ℕ) {c V η : ℝ} (hc : 0 < c) (hV : 0 < V) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ R, 0 < R → R ≤ 1 →
      ∀ t, 0 < t → t < δ * R ^ 2 → ∀ x y,
      c * R ≤ dist x y →
      V * (Real.sqrt t) ^ n ≤ μ.real (ball y (Real.sqrt t)) →
      R ^ n * |ker t x y| ≤ η := by
  obtain ⟨C, b, hC, hb, hgauss⟩ := hg (1 / 2) (by norm_num) (by norm_num)
  have ha : 0 < c ^ 2 / (4 + 1 / 2 : ℝ) := by positivity
  have hlim := (gaussianOffDiagonalEnvelope_tendsto ((n : ℝ) / 2) b ha).const_mul (C / V)
  obtain ⟨δ₀, hδ₀, hnear⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim η hη
  refine ⟨min δ₀ 1, lt_min hδ₀ zero_lt_one, min_le_right _ _, ?_⟩
  intro R hR hR1 t ht htδ x y hsep hvol
  have hτ : 0 < t / R ^ 2 := div_pos ht (sq_pos_of_pos hR)
  have hτδ : t / R ^ 2 < δ₀ :=
    ((div_lt_iff₀ (sq_pos_of_pos hR)).mpr htδ).trans_le (min_le_left _ _)
  have hvol' : V / (t⁻¹) ^ ((n : ℝ) / 2) ≤ μ.real (ball y (Real.sqrt t)) := by
    simpa only [inverse_power_sqrt n ht, div_inv_eq_mul] using hvol
  have hu := gaussian_upper_of_inverse_power_volume μ ker ht (mul_pos hc hR).le
    hC hV (by norm_num : (0 : ℝ) < 4 + 1 / 2) x y (hgauss t ht x y).2 hvol' hsep
  have hs := gaussian_envelope_scale n (c := c) (D := 4 + 1 / 2) hR hR1 ht hb
  have hsmall : (C / V) * gaussianOffDiagonalEnvelope ((n : ℝ) / 2)
      (c ^ 2 / (4 + 1 / 2)) b (t / R ^ 2) < η := by
    have hh := hnear hτ (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hτ] using hτδ)
    exact (le_abs_self _).trans_lt (by simpa only [Real.dist_eq, mul_zero, sub_zero] using hh)
  rw [abs_of_nonneg (hnonneg t ht x y)]
  calc
    _ ≤ R ^ n * ((C / V) * gaussianOffDiagonalEnvelope ((n : ℝ) / 2)
        ((c * R) ^ 2 / (4 + 1 / 2)) b t) :=
      mul_le_mul_of_nonneg_left hu (pow_nonneg hR.le _)
    _ = (C / V) * (R ^ n * gaussianOffDiagonalEnvelope ((n : ℝ) / 2)
        ((c * R) ^ 2 / (4 + 1 / 2)) b t) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (div_pos hC hV).le
    _ ≤ η := hsmall.le

end RegularPointCoordinates

end

end OAI
