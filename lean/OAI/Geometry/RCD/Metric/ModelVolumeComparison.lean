import OAI.Geometry.RCD.Metric.IntegratedRCDVolume

namespace OAI

/-! # The required model Bishop--Gromov comparison from the actual CD condition

The proof integrates the annular transport inequality. The preliminary
radial comparison supplies absolute continuity and null spheres, so this
does not assume any instance of model-volume monotonicity.
-/

open Set Metric MeasureTheory

namespace RegularPointCoordinates

theorem comparisonModelVolume_sinh_normalization (m : ℕ) {a : ℝ} (ha : 0 < a) (R : ℝ) :
    a ^ m * comparisonModelVolume m a R =
      (m + 1 : ℝ) * ∫ t in 0..R, Real.sinh (t * a) ^ m := by
  have hrad (t : ℝ) : a * radialComparison a t = Real.sinh (t * a) := by
    rw [radialComparison_eq_sinh ha.ne']
    field_simp
  have hpow (t : ℝ) : a ^ m * radialComparison a t ^ m = Real.sinh (t * a) ^ m := by
    rw [← mul_pow, hrad]
  calc
    _ = (m + 1 : ℝ) * (a ^ m * ∫ t in 0..R, radialComparison a t ^ m) := by
      unfold comparisonModelVolume
      ring
    _ = (m + 1 : ℝ) * ∫ t in 0..R, a ^ m * radialComparison a t ^ m := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by simp_rw [hpow]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.negative_model_ballVolumeComparison {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K < 0) :
    BallVolumeComparison (hausdorff n X)
      (comparisonModelVolume (n - 1) (Real.sqrt (-K / ((n : ℝ) - 1)))) := by
  intro p r R hr hrR
  let a := Real.sqrt (-K / ((n : ℝ) - 1))
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hK) (sub_pos.mpr hn1))
  have h := hX.hyperbolic_integral_ball_comparison hn hK p hr hrR
  have hsmall := comparisonModelVolume_sinh_normalization (n - 1) ha r
  have hlarge := comparisonModelVolume_sinh_normalization (n - 1) ha R
  apply (mul_le_mul_iff_right₀ (pow_pos ha (n - 1))).mp
  calc
    _ = (((n - 1 : ℕ) : ℝ) + 1) * ((hausdorff n X).real (ball p R) *
        ∫ t in 0..r, Real.sinh (t * a) ^ (n - 1)) := by
      calc
        _ = (hausdorff n X).real (ball p R) *
            (a ^ (n - 1) * comparisonModelVolume (n - 1) a r) := by ring
        _ = _ := by rw [hsmall]; ring
    _ ≤ (((n - 1 : ℕ) : ℝ) + 1) * ((hausdorff n X).real (ball p r) *
        ∫ t in 0..R, Real.sinh (t * a) ^ (n - 1)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      calc
        _ = (hausdorff n X).real (ball p r) *
            (a ^ (n - 1) * comparisonModelVolume (n - 1) a R) := by rw [hlarge]; ring
        _ = _ := by ring

theorem NoncollapsedRCD.exists_model_ballVolumeComparison {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ a : ℝ, 0 ≤ a ∧
      BallVolumeComparison (hausdorff n X) (comparisonModelVolume (n - 1) a) := by
  by_cases hK : 0 ≤ K
  · exact ⟨0, le_rfl, hX.zero_model_ballVolumeComparison hn hK⟩
  · have hKneg : K < 0 := lt_of_not_ge hK
    exact ⟨Real.sqrt (-K / ((n : ℝ) - 1)), Real.sqrt_nonneg _,
      hX.negative_model_ballVolumeComparison hn hKneg⟩

end RegularPointCoordinates

end OAI
