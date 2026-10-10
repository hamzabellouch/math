import OAI.Probability.SLE.Multipoint.MultipointGeometry
import OAI.Probability.SLE.AngularLaws

namespace OAI

/-! Compact disk-chart bounds used to compare physical cell mass with
canonical disk mass. Coarse universal constants suffice for the gauge bounds. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma univalent_ball_subset_image
    {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball 0 r)) (hi : InjOn f (ball 0 r)) :
    ball (f 0) (r * ‖deriv f 0‖ / (128 * Real.pi)) ⊆ f '' ball 0 r := by
  intro z hz
  by_contra hn
  have h := univalent_omitted_value_bound_ball hr hd hi z hn
  have hp : 0 < 128 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hz' : dist z (f 0) < r * ‖deriv f 0‖ / (128 * Real.pi) := hz
  have hh := (lt_div_iff₀ hp).mp hz'
  rw [dist_eq_norm, norm_sub_rev] at hh
  nlinarith

lemma univalent_half_growth_bound (hgrowth : PublishedDiskUnivalentGrowth)
    {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hi : InjOn f (ball 0 1)) {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖f z - f 0‖ ≤ 2 * ‖deriv f 0‖ := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hh := hgrowth f hd hi z (mem_ball_zero_iff.mpr hz1)
  apply hh.trans
  have hp : 0 < (1-‖z‖)^2 := sq_pos_of_pos (by linarith)
  apply (div_le_iff₀ hp).mpr
  have hsq : (1/4:ℝ) ≤ (1-‖z‖)^2 := by nlinarith [norm_nonneg z]
  have hprod := mul_le_mul_of_nonneg_left hsq (norm_nonneg (deriv f 0))
  have hnorm := mul_le_mul_of_nonneg_left hz (norm_nonneg (deriv f 0))
  nlinarith

lemma univalent_quarter_derivative_upper (hgrowth : PublishedDiskUnivalentGrowth)
    {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hi : InjOn f (ball 0 1)) {z : ℂ} (hz : ‖z‖ ≤ 1/4) :
    ‖deriv f z‖ ≤ 16 * ‖deriv f 0‖ := by
  have hsub : ball z (1/4) ⊆ ball (0:ℂ) 1 := by
    intro w hw
    have hdist : ‖w-z‖ < 1/4 := by simpa only [mem_ball,dist_eq_norm] using hw
    have hnorm : ‖w‖ ≤ ‖w-z‖+‖z‖ := by simpa only [norm_sub_rev, add_comm] using norm_le_insert z w
    apply mem_ball_zero_iff.mpr
    linarith
  have hmaps : MapsTo f (ball z (1/4)) (closedBall (f z) (4*‖deriv f 0‖)) := by
    intro w hw
    have hdist : ‖w-z‖ < 1/4 := by simpa only [mem_ball,dist_eq_norm] using hw
    have hnorm : ‖w‖ ≤ ‖w-z‖+‖z‖ := by simpa only [norm_sub_rev, add_comm] using norm_le_insert z w
    have hw2 : ‖w‖ ≤ 1/2 := by linarith
    have hz2 : ‖z‖ ≤ 1/2 := by linarith
    have hb₁ := univalent_half_growth_bound hgrowth hd hi hw2
    have hb₂ := univalent_half_growth_bound hgrowth hd hi hz2
    have htri : ‖f w-f z‖ ≤ ‖f w-f 0‖+‖f z-f 0‖ := by
      simpa only [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub (f w) (f 0) (f z)
    change dist (f w) (f z) ≤ 4*‖deriv f 0‖
    rw [dist_eq_norm]
    linarith
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball (hd.mono hsub) hmaps (by norm_num : (0:ℝ)<1/4)
  norm_num at hh ⊢
  linarith

lemma univalent_quarter_closed_image_contains
    {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hi : InjOn f (ball 0 1)) (hder : 0 < ‖deriv f 0‖) :
    closedBall (f 0) (‖deriv f 0‖ / (1024 * Real.pi)) ⊆
      f '' closedBall 0 (1/4) := by
  have hsub : ball (0:ℂ) (1/4) ⊆ ball 0 1 := ball_subset_ball (by norm_num)
  have h := univalent_ball_subset_image (by norm_num : (0:ℝ)<1/4) (hd.mono hsub) (hi.mono hsub)
  intro z hz
  apply (image_mono ball_subset_closedBall)
  apply h
  have hp : 0 < Real.pi := Real.pi_pos
  have hstrict : ‖deriv f 0‖ / (1024 * Real.pi) < (1/4)*‖deriv f 0‖ / (128 * Real.pi) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  exact lt_of_le_of_lt hz hstrict

lemma univalent_quarter_closed_image_bound (hgrowth : PublishedDiskUnivalentGrowth)
    {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hi : InjOn f (ball 0 1)) :
    f '' closedBall 0 (1/4) ⊆ closedBall (f 0) (2*‖deriv f 0‖) := by
  rintro z ⟨w,hw,rfl⟩
  have hw' : ‖w‖ ≤ 1/2 := by
    have hh : ‖w‖ ≤ 1/4 := by simpa only [mem_closedBall,dist_zero_right] using hw
    linarith
  simpa only [mem_closedBall,dist_eq_norm] using univalent_half_growth_bound hgrowth hd hi hw'

end SLEExactGauge

end

end OAI
