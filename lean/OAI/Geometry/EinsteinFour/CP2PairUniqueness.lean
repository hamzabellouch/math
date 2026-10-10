import OAI.Geometry.EinsteinFour.CP2WeightedBessel

namespace OAI

/-! The unique top line of the sum of two nonorthogonal rank-one projections.
Only this two-vector specialization is needed for the CP2 involution argument. -/

namespace PositiveEinsteinFour

open EinsteinFour

noncomputable section

private theorem cp2_aligned_pair_data (p q : CP2Vector) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hc : inner ℂ p q = (c : ℂ)) :
    ‖p + q‖ ^ 2 = 2 + 2 * c ∧ ‖p - q‖ ^ 2 = 2 - 2 * c ∧
      inner ℂ (p + q) (p - q) = 0 := by
  have hqp : inner ℂ q p = (c : ℂ) := by rw [← inner_conj_symm, hc]; simp
  constructor
  · rw [norm_add_sq (𝕜 := ℂ), hp, hq, hc]
    simp
    ring
  constructor
  · rw [norm_sub_sq (𝕜 := ℂ), hp, hq, hc]
    simp
    ring
  · simp only [inner_add_left, inner_sub_right, inner_self_eq_norm_sq_to_K, hp, hq,
      hc, hqp]
    ring

theorem cp2_aligned_pair_top_unique (p q w : CP2Vector) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hw : ‖w‖ = 1)
    (hc : inner ℂ p q = (c : ℂ)) (hc0 : 0 < c) (hc1 : c < 1)
    (htop : ‖inner ℂ p w‖ ^ 2 + ‖inner ℂ q w‖ ^ 2 = 1 + c) :
    ∃ a : ℂ, a ≠ 0 ∧ w = a • (p + q) := by
  obtain ⟨hplus, hminus, horth⟩ := cp2_aligned_pair_data p q c hp hq hc
  have hd1 : 0 < 2 + 2 * c := by linarith
  have hd2 : 0 < 2 - 2 * c := by linarith
  have hu : p + q ≠ 0 := by intro h; rw [h, norm_zero] at hplus; nlinarith
  have hv : p - q ≠ 0 := by intro h; rw [h, norm_zero] at hminus; nlinarith
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; exact zero_ne_one hw
  have hb := cp2_weighted_bessel (p + q) (p - q) w hu hv horth
  rw [hplus, hminus, hw, one_pow] at hb
  have hpar : ‖inner ℂ (p + q) w‖ ^ 2 + ‖inner ℂ (p - q) w‖ ^ 2 = 2 + 2 * c := by
    rw [inner_add_left, inner_sub_left]
    have h := parallelogram_law_with_norm ℂ (inner ℂ p w) (inner ℂ q w)
    rw [htop] at h
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hb (mul_nonneg hd1.le hd2.le)
  have halg :
      (‖inner ℂ (p + q) w‖ ^ 2 / (2 + 2 * c) +
        ‖inner ℂ (p - q) w‖ ^ 2 / (2 - 2 * c)) * ((2 + 2 * c) * (2 - 2 * c)) =
      ‖inner ℂ (p + q) w‖ ^ 2 * (2 - 2 * c) +
        ‖inner ℂ (p - q) w‖ ^ 2 * (2 + 2 * c) := by
    have hcancel (A B d e : ℝ) (hd : d ≠ 0) (he : e ≠ 0) :
        (A / d + B / e) * (d * e) = A * e + B * d := by
      field_simp
    exact hcancel _ _ _ _ hd1.ne' hd2.ne'
  rw [halg, one_mul] at hmul
  have hz : ‖inner ℂ (p - q) w‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖inner ℂ (p - q) w‖]
  have hCS : ‖inner ℂ (p + q) w‖ = ‖p + q‖ * ‖w‖ := by
    rw [hw, mul_one]
    nlinarith [norm_nonneg (inner ℂ (p + q) w), norm_nonneg (p + q)]
  exact (norm_inner_eq_norm_iff hu hw0).mp hCS

end
end PositiveEinsteinFour

end OAI
