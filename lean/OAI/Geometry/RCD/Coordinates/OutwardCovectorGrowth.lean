import OAI.Geometry.RCD.Coordinates.DyadicCovectorGrowth

namespace OAI

/-! # The complementary growth bound for shrinking-scale covectors -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The other half of the same adjacent mean comparison bounds smaller
scale covectors by the original one. Together with shrinking radii this
makes the center values of the actual affine fits tend to zero. -/
theorem dyadic_covector_norm_reverse_growth {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 1) X) {a R ε : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
    (p : X) (hR : 0 < R) (hscale : a * (3 * R) ≤ 1) (hε : 0 ≤ ε)
    (hsmall : ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * ε) ≤ 1 / 64)
    (S : ℕ → Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
    (hexact : ∀ i, IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
      (ball p (R / 2 ^ i)) measurableSet_ball (S i))
    (hfirst : ∀ i, ∃ w : X → Euclidean (m + 1),
      FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (R / 2 ^ i) ε
        (transformedColumn (hausdorff (m + 1) X) hX.quadratic u (S i)) w) :
    ∀ i k (b : Euclidean (m + 1)),
      ‖(S (i + k)).symm b‖ ≤ (9 / 8 : ℝ) ^ k * ‖(S i).symm b‖ := by
  let μ := hausdorff (m + 1) X
  have hstep (i : ℕ) (b : Euclidean (m + 1)) :
      ‖(S (i + 1)).symm b‖ ≤ (9 / 8 : ℝ) * ‖(S i).symm b‖ := by
    have hr : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
    have hrR : R / (2 : ℝ) ^ i ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
    have hscaled : a * (3 * ((R / (2 : ℝ) ^ i) / 2)) ≤ 1 := by
      exact (mul_le_mul_of_nonneg_left (show 3 * ((R / (2 : ℝ) ^ i) / 2) ≤ 3 * R by linarith) ha).trans hscale
    obtain ⟨w, hw⟩ := hfirst i
    have hh := (normalized_adjacent_mean_comparison m hX ha hBG u (S i) hr hscaled hε hw (hexact i) b).2
    have hnext : (R / (2 : ℝ) ^ i) / 2 = R / 2 ^ (i + 1) := by
      rw [pow_succ]
      field_simp
    rw [hnext] at hh
    rw [← exact_mean_inverse_norm_sq μ hX.quadratic _ _ measurableSet_ball (S i) (hexact i) b,
      ← exact_mean_inverse_norm_sq μ hX.quadratic _ _ measurableSet_ball (S (i + 1)) (hexact (i + 1)) b] at hh
    have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖(S i).symm b‖)
    have hsq : ‖(S (i + 1)).symm b‖ ^ 2 ≤ ((9 / 8 : ℝ) * ‖(S i).symm b‖) ^ 2 := by
      nlinarith [sq_nonneg ‖(S i).symm b‖]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
  intro i k b
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 9 / 8)
    calc
      _ ≤ (9 / 8 : ℝ) * ‖(S (i + k)).symm b‖ := by
        simpa only [Nat.add_assoc] using hstep (i + k) b
      _ ≤ (9 / 8 : ℝ) * ((9 / 8 : ℝ) ^ k * ‖(S i).symm b‖) := hh
      _ = _ := by rw [pow_succ]; ring

end RegularPointCoordinates

end

end OAI
