import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.WellCapRegularity

namespace OAI

/-! Uniform quantitative bounds on the two derivatives of the rational cap. -/

noncomputable section
open Set Filter
open scoped Topology
namespace ContinuumCoulomb

private theorem cap_local_zero {t : ℝ} (ht : t < 1 / 16) :
    wellCap =ᶠ[𝓝 t] fun _ => 0 := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact wellCap_eq_zero hs.le

private theorem cap_local_one {t : ℝ} (ht : 1 / 8 < t) :
    wellCap =ᶠ[𝓝 t] fun _ => 1 := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact wellCap_eq_one hs.le

private theorem cap_local_middle {t : ℝ} (ht0 : 1 / 16 < t) (ht1 : t < 1 / 8) :
    wellCap =ᶠ[𝓝 t] fun s => wellTransition (16 * s - 1) := by
  filter_upwards [Ioi_mem_nhds ht0, Iio_mem_nhds ht1] with s hs0 hs1
  change 1 / 16 < s at hs0
  change s < 1 / 8 at hs1
  simp only [wellCap, ite_eq_right (not_le.mpr hs0), ite_eq_right (not_le.mpr hs1)]

theorem wellCap_deriv_zero_left {t : ℝ} (ht : t ≤ 1 / 16) : deriv wellCap t = 0 := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · rw [(cap_local_zero hlt).deriv_eq]
    simp
  · subst t
    have hmin : IsLocalMin wellCap (1 / 16) := by
      apply Filter.Eventually.of_forall
      intro s
      rw [wellCap_eq_zero (le_refl _)]
      exact (wellCap_bounds s).1
    exact hmin.deriv_eq_zero

theorem wellCap_deriv_zero_right {t : ℝ} (ht : 1 / 8 ≤ t) : deriv wellCap t = 0 := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · rw [(cap_local_one hlt).deriv_eq]
    simp
  · subst t
    have hmax : IsLocalMax wellCap (1 / 8) := by
      apply Filter.Eventually.of_forall
      intro s
      rw [wellCap_eq_one (le_refl _)]
      exact (wellCap_bounds s).2
    exact hmax.deriv_eq_zero

private theorem middle_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => wellTransition (16 * s - 1))
      (480 * (16 * t - 1) ^ 2 * (16 * t - 2) ^ 2) t := by
  have hlin := ((hasDerivAt_id t).const_mul 16).sub_const 1
  convert (((hlin.pow 5).const_mul 6).sub ((hlin.pow 4).const_mul 15)).add
    ((hlin.pow 3).const_mul 10) using 1 <;> (try funext y) <;>
      (dsimp [wellTransition]; all_goals ring)

private theorem middlePrime_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => 480 * (16 * s - 1) ^ 2 * (16 * s - 2) ^ 2)
      (15360 * (16 * t - 1) * (16 * t - 2) * (32 * t - 3)) t := by
  have hlin := ((hasDerivAt_id t).const_mul 16).sub_const 1
  have hlin' := ((hasDerivAt_id t).const_mul 16).sub_const 2
  convert ((hlin.pow 2).const_mul 480).mul (hlin'.pow 2) using 1 <;>
    (try funext y) <;> (dsimp; all_goals ring)

theorem wellCap_deriv_inside {t : ℝ} (ht0 : 1 / 16 < t) (ht1 : t < 1 / 8) :
    deriv wellCap t = 480 * (16 * t - 1) ^ 2 * (16 * t - 2) ^ 2 := by
  rw [(cap_local_middle ht0 ht1).deriv_eq]
  exact (middle_hasDerivAt t).deriv

theorem wellCap_deriv_bounds (t : ℝ) : 0 ≤ deriv wellCap t ∧ deriv wellCap t ≤ 480 := by
  by_cases h0 : t ≤ 1 / 16
  · rw [wellCap_deriv_zero_left h0]
    norm_num
  by_cases h1 : 1 / 8 ≤ t
  · rw [wellCap_deriv_zero_right h1]
    norm_num
  rw [wellCap_deriv_inside (lt_of_not_ge h0) (lt_of_not_ge h1)]
  have hs0 : 0 ≤ 16 * t - 1 := by linarith
  have hs1 : 16 * t - 1 ≤ 1 := by linarith
  have ha : (16 * t - 1) ^ 2 ≤ 1 := by nlinarith
  have hb : (16 * t - 2) ^ 2 ≤ 1 := by nlinarith
  have hab := mul_le_mul ha hb (sq_nonneg (16 * t - 2)) (by norm_num : (0 : ℝ) ≤ 1)
  constructor
  · positivity
  · nlinarith

theorem wellCap_deriv2_zero_left {t : ℝ} (ht : t ≤ 1 / 16) :
    deriv (deriv wellCap) t = 0 := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · rw [(cap_local_zero hlt).deriv.deriv_eq]
    simp
  · subst t
    have hmin : IsLocalMin (deriv wellCap) (1 / 16) := by
      apply Filter.Eventually.of_forall
      intro s
      rw [wellCap_deriv_zero_left (le_refl _)]
      exact (wellCap_deriv_bounds s).1
    exact hmin.deriv_eq_zero

theorem wellCap_deriv2_zero_right {t : ℝ} (ht : 1 / 8 ≤ t) :
    deriv (deriv wellCap) t = 0 := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · rw [(cap_local_one hlt).deriv.deriv_eq]
    simp
  · subst t
    have hmin : IsLocalMin (deriv wellCap) (1 / 8) := by
      apply Filter.Eventually.of_forall
      intro s
      rw [wellCap_deriv_zero_right (le_refl _)]
      exact (wellCap_deriv_bounds s).1
    exact hmin.deriv_eq_zero

theorem wellCap_deriv2_inside {t : ℝ} (ht0 : 1 / 16 < t) (ht1 : t < 1 / 8) :
    deriv (deriv wellCap) t =
      15360 * (16 * t - 1) * (16 * t - 2) * (32 * t - 3) := by
  rw [(cap_local_middle ht0 ht1).deriv.deriv_eq]
  have heq : deriv (fun s => wellTransition (16 * s - 1)) =
      fun s => 480 * (16 * s - 1) ^ 2 * (16 * s - 2) ^ 2 := by
    funext s
    exact (middle_hasDerivAt s).deriv
  rw [heq]
  exact (middlePrime_hasDerivAt t).deriv

theorem wellCap_deriv2_bound (t : ℝ) : |deriv (deriv wellCap) t| ≤ 15360 := by
  by_cases h0 : t ≤ 1 / 16
  · rw [wellCap_deriv2_zero_left h0]
    norm_num
  by_cases h1 : 1 / 8 ≤ t
  · rw [wellCap_deriv2_zero_right h1]
    norm_num
  rw [wellCap_deriv2_inside (lt_of_not_ge h0) (lt_of_not_ge h1)]
  have ha : |16 * t - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hb : |16 * t - 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hc : |32 * t - 3| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hab := mul_le_mul ha hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have habc := mul_le_mul hab hc (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 15360)]
  nlinarith

theorem wellCap_lipschitz : LipschitzWith 480 wellCap := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (wellCap_contDiff_two.differentiable (by norm_num))
  intro t
  change ‖deriv wellCap t‖ ≤ (480 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (wellCap_deriv_bounds t).1]
  exact (wellCap_deriv_bounds t).2

theorem wellCap_deriv_lipschitz : LipschitzWith 15360 (deriv wellCap) := by
  have h : ContDiff ℝ 1 (deriv wellCap) := wellCap_contDiff_two.deriv'
  apply lipschitzWith_of_nnnorm_deriv_le (h.differentiable (by norm_num))
  intro t
  change ‖deriv (deriv wellCap) t‖ ≤ (15360 : ℝ)
  simpa only [Real.norm_eq_abs] using wellCap_deriv2_bound t

theorem radial_wellCap_difference {D : ℝ} (hD : 0 < D) (center x y : Position) :
    |wellCap (‖x - center‖ / D) - wellCap (‖y - center‖ / D)| ≤
      (480 / D) * ‖x - y‖ := by
  have hcap := wellCap_lipschitz.dist_le_mul (‖x - center‖ / D) (‖y - center‖ / D)
  have hrad : |‖x - center‖ / D - ‖y - center‖ / D| ≤ ‖x - y‖ / D := by
    rw [← sub_div, abs_div, abs_of_pos hD]
    apply div_le_div_of_nonneg_right _ hD.le
    have h := abs_norm_sub_norm_le (x - center) (y - center)
    have he : (x - center) - (y - center) = x - y := by abel
    simpa only [he] using h
  have hc : |wellCap (‖x - center‖ / D) - wellCap (‖y - center‖ / D)| ≤
      480 * |‖x - center‖ / D - ‖y - center‖ / D| := by
    simpa only [Real.dist_eq, NNReal.coe_ofNat] using hcap
  apply hc.trans
  calc
    _ ≤ 480 * (‖x - y‖ / D) := mul_le_mul_of_nonneg_left hrad (by norm_num)
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
