import OAI.Analysis.AllenCahn.DriftMaximum

namespace OAI

noncomputable section
namespace DriftSupport.DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open MeasureTheory
open scoped ENNReal

private lemma no_tangent_zero_drift {n : ℕ} {w : Space n → ℝ}
    (b : Space n → Space n) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, ‖b x‖ ≤ B)
    (hw : ContDiff ℝ 2 w) (hw0 : ∀ x, 0 ≤ w x)
    (hineq : ∀ x, Laplacian.laplacian w x ≤ 2 * w x + fderiv ℝ w x (b x))
    {r : ℝ} (hr : 0 < r) (y z : Space n) (hz : ‖z - y‖ = r)
    (hwz : w z = 0) (hball : ∀ x, ‖x - y‖ < r → 0 < w x) : False := by
  obtain ⟨p, hp, hpmin⟩ := (isCompact_closedBall y (r / 2)).exists_isMinOn
    ⟨y, by simp only [Metric.mem_closedBall, dist_self]; positivity⟩ hw.continuous.continuousOn
  have hppos : 0 < w p := hball p (by
    have hnorm : ‖p - y‖ ≤ r / 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hp
    linarith)
  let a : ℝ := 1 + (2 * (n : ℝ) + 2 + 2 * B * r) / r ^ 2
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have ha : 1 ≤ a := by
    have hq : 0 ≤ (2 * (n : ℝ) + 2 + 2 * B * r) / r ^ 2 := by positivity
    dsimp [a]
    linarith
  have hscale : 2 * (n : ℝ) + 2 + 2 * B * r ≤ a * r ^ 2 := by
    dsimp [a]
    field_simp
    nlinarith
  have hcomp := annulus_comparison_drift b hB hb hw hw0 hineq ha hr hppos.le hscale y
    (fun x hx => hpmin (by simp [Metric.mem_closedBall, dist_eq_norm, hx]))
  let F : Space n → ℝ := fun x => w x - w p * barrier a r y x
  let e : Space n := y - z
  let f : ℝ → ℝ := fun t => F (z + t • e)
  have hF : ContDiff ℝ 2 F := hw.sub (contDiff_const.mul (barrier_contDiff a r y))
  have hdline : HasDerivAt (fun t : ℝ => z + t • e) e 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) z).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const e)
  have hd : HasDerivAt f (fderiv ℝ F z e) 0 := by
    simpa [f, Function.comp_def] using ((hF.differentiable (by norm_num) (z + (0 : ℝ) • e)).hasFDerivAt.comp_hasDerivAt 0 hdline)
  have hf0 : f 0 = 0 := by simp [f, F, barrier, gaussian, hz, hwz]
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f t := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with t ht ht2
    change 0 < t at ht
    change t < 1 / 2 at ht2
    have hnorm : ‖z + t • e - y‖ = (1 - t) * r := by
      have heq : z + t • e - y = (1 - t) • (z - y) := by dsimp [e]; module
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 - t), hz]
    have hlow : r / 2 ≤ ‖z + t • e - y‖ := by rw [hnorm]; nlinarith
    have hhigh : ‖z + t • e - y‖ ≤ r := by rw [hnorm]; nlinarith
    have hh := hcomp (z + t • e) hlow hhigh
    dsimp [f, F]
    linarith
  have hnonneg := nonneg_right_derivative hd hf0 hpos
  have hmin : IsLocalMin w z := Filter.Eventually.of_forall (fun x => by simpa [hwz] using hw0 x)
  have hwder := hmin.fderiv_eq_zero
  have hi : inner ℝ (z - y) e = -r ^ 2 := by
    have heq : e = -(z - y) := by dsimp [e]; abel
    rw [heq, inner_neg_right, real_inner_self_eq_norm_sq, hz]
  have hcalc : fderiv ℝ F z e =
      -(w p * gaussian a y z * (2 * a * r ^ 2)) := by
    dsimp only [F]
    rw [fderiv_fun_sub (hw.differentiable (by norm_num) z)
      (((barrier_contDiff a r y).differentiable (by norm_num)).const_mul _ z)]
    simp only [sub_apply, hwder, zero_apply]
    rw [fderiv_const_mul ((barrier_contDiff a r y).differentiable (by norm_num) z)]
    simp only [smul_apply, smul_eq_mul]
    rw [fderiv_barrier, hi]
    ring
  have hnegative : fderiv ℝ F z e < 0 := by
    rw [hcalc]
    have hg : 0 < gaussian a y z := Real.exp_pos _
    have hap : 0 < a := lt_of_lt_of_le (by norm_num) ha
    exact neg_neg_of_pos (mul_pos (mul_pos hppos hg) (mul_pos (mul_pos (by norm_num) hap) hr2))
  exact not_le_of_gt hnegative hnonneg

lemma nonnegative_supersolution_eq_zero_drift {n : ℕ} {w : Space n → ℝ}
    (b : Space n → Space n) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, ‖b x‖ ≤ B)
    (hw : ContDiff ℝ 2 w) (hw0 : ∀ x, 0 ≤ w x)
    (hineq : ∀ x, Laplacian.laplacian w x ≤ 2 * w x + fderiv ℝ w x (b x))
    {z : Space n} (hwz : w z = 0) : ∀ x, w x = 0 := by
  intro y
  by_contra hy
  have hypos : 0 < w y := lt_of_le_of_ne (hw0 y) (Ne.symm hy)
  let Z : Set (Space n) := {x | w x = 0}
  have hZ : IsClosed Z := isClosed_eq hw.continuous continuous_const
  obtain ⟨p, hp, hdist⟩ := hZ.exists_infDist_eq_dist ⟨z, hwz⟩ y
  have hne : y ≠ p := by
    intro heq
    have hpzero : w p = 0 := hp
    rw [heq, hpzero] at hypos
    exact lt_irrefl _ hypos
  have hr : 0 < dist y p := dist_pos.mpr hne
  have hball : ∀ x, ‖x - y‖ < dist y p → 0 < w x := by
    intro x hx
    by_contra hnot
    have hwx : w x = 0 := le_antisymm (le_of_not_gt hnot) (hw0 x)
    have hd := Metric.infDist_le_dist_of_mem (x := y) (show x ∈ Z from hwx)
    rw [hdist] at hd
    have he : dist y x = ‖x - y‖ := by rw [dist_comm, dist_eq_norm]
    rw [he] at hd
    exact not_le_of_gt hx hd
  exact no_tangent_zero_drift b hB hb hw hw0 hineq hr y p (by rw [← dist_eq_norm, dist_comm]) hp hball

end DriftSupport.DeGiorgi
end

end OAI
