import OAI.Geometry.RCD.Coordinates.AdjacentMeanComparison

namespace OAI

/-! # Slow growth of covectors in the same exact dyadic frames -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Exact normalization converts the adjacent mean comparison directly
into slow growth of the covector norm used by the radial fit recurrence. -/
theorem dyadic_covector_norm_growth {K : ℝ} (m : ℕ)
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
      ‖(S i).symm b‖ ≤ (9 / 8 : ℝ) ^ k * ‖(S (i + k)).symm b‖ := by
  let μ := hausdorff (m + 1) X
  have hstep (i : ℕ) (b : Euclidean (m + 1)) :
      ‖(S i).symm b‖ ≤ (9 / 8 : ℝ) * ‖(S (i + 1)).symm b‖ := by
    have hr : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
    have hrR : R / (2 : ℝ) ^ i ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
    have hscaled : a * (3 * ((R / (2 : ℝ) ^ i) / 2)) ≤ 1 := by
      apply le_trans (mul_le_mul_of_nonneg_left (show 3 * ((R / (2 : ℝ) ^ i) / 2) ≤ 3 * R by linarith) ha) hscale
    obtain ⟨w, hw⟩ := hfirst i
    have hh := (normalized_adjacent_mean_comparison m hX ha hBG u (S i) hr hscaled hε hw (hexact i) b).1
    have hnext : (R / (2 : ℝ) ^ i) / 2 = R / 2 ^ (i + 1) := by
      rw [pow_succ]
      field_simp
    rw [hnext] at hh
    rw [← exact_mean_inverse_norm_sq μ hX.quadratic _ _ measurableSet_ball (S i) (hexact i) b,
      ← exact_mean_inverse_norm_sq μ hX.quadratic _ _ measurableSet_ball (S (i + 1)) (hexact (i + 1)) b] at hh
    have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖(S i).symm b‖)
    have hsq : ‖(S i).symm b‖ ^ 2 ≤ ((9 / 8 : ℝ) * ‖(S (i + 1)).symm b‖) ^ 2 := by
      nlinarith [sq_nonneg ‖(S (i + 1)).symm b‖]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
  intro i k b
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := mul_le_mul_of_nonneg_left (hstep (i + k) b) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 8) k)
    calc
      _ ≤ (9 / 8 : ℝ) ^ k * ‖(S (i + k)).symm b‖ := ih
      _ ≤ (9 / 8 : ℝ) ^ k * ((9 / 8 : ℝ) * ‖(S (i + k + 1)).symm b‖) := hh
      _ = _ := by simp only [Nat.add_assoc, pow_succ]; ring

end RegularPointCoordinates

end

end OAI
