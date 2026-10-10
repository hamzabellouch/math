import OAI.Geometry.RCD.Harmonic.ExactAnnularContraction

namespace OAI

/-! # Real-valued sharp annular volume comparison

The coefficient is the radial area density of the negative-curvature model.
No model-volume comparison is assumed in obtaining this inequality.
-/

open Set Metric MeasureTheory

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.annular_volume_ratio {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K < 0) (p : X)
    {r R t : ℝ} (hr : 0 < r) (hrR : r < R) (ht : 0 < t) (ht1 : t < 1) :
    let a := Real.sqrt (-K / ((n : ℝ) - 1))
    (t * Real.sinh (t * R * a) ^ (n - 1)) *
        (hausdorff n X).real (ball p R \ closedBall p r) ≤
      Real.sinh (R * a) ^ (n - 1) *
        (hausdorff n X).real (ball p (t * R) \ closedBall p (t * r)) := by
  dsimp only
  let a := Real.sqrt (-K / ((n : ℝ) - 1))
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hK) (sub_pos.mpr hn1))
  have hR : 0 < R := hr.trans hrR
  have hlarge : 0 < Real.sinh (R * a) := Real.sinh_pos_iff.mpr (mul_pos hR ha)
  have hsmall : 0 < Real.sinh (t * R * a) :=
    Real.sinh_pos_iff.mpr (mul_pos (mul_pos ht hR) ha)
  have h := hX.exact_annular_contraction hn hK p hr hrR ht ht1
  rw [tau_nat_power hn ht ht1, sigma_neg_eq hK hn1 hR] at h
  have hreal := ENNReal.toReal_mono
    (hX.finiteOnBounded _ (isBounded_ball.subset sdiff_subset)).ne h
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal ht.le,
    ENNReal.toReal_ofReal (div_pos hsmall hlarge).le] at hreal
  change (t * (Real.sinh (t * R * a) / Real.sinh (R * a)) ^ (n - 1)) *
      (hausdorff n X).real (ball p R \ closedBall p r) ≤
    (hausdorff n X).real (ball p (t * R) \ closedBall p (t * r)) at hreal
  change (t * Real.sinh (t * R * a) ^ (n - 1)) *
      (hausdorff n X).real (ball p R \ closedBall p r) ≤
    Real.sinh (R * a) ^ (n - 1) *
      (hausdorff n X).real (ball p (t * R) \ closedBall p (t * r))
  calc
    _ = ((t * (Real.sinh (t * R * a) / Real.sinh (R * a)) ^ (n - 1)) *
        (hausdorff n X).real (ball p R \ closedBall p r)) *
          Real.sinh (R * a) ^ (n - 1) := by
      rw [div_pow]
      field_simp
    _ ≤ (hausdorff n X).real (ball p (t * R) \ closedBall p (t * r)) *
        Real.sinh (R * a) ^ (n - 1) :=
      mul_le_mul_of_nonneg_right hreal (pow_nonneg hlarge.le _)
    _ = _ := mul_comm _ _

end RegularPointCoordinates

end OAI
