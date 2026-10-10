import OAI.Analysis.AllenCahn.Cutoffs

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open scoped ContDiff
open Filter Topology

lemma unbounded_bernstein_bound {n : ℕ} {w : Space n → ℝ}
    (hw : ContDiff ℝ 2 w) (hw0 : ∀ x, 0 ≤ w x) (b : Space n → Space n)
    {L p B C : ℝ} (hL : 0 ≤ L) (hp : 0 ≤ p) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, ‖b x‖ ≤ B + C * Real.sqrt (w x))
    (heq : ∀ x, w x ^ 2 ≤ L * (1 + w x) +
      p * (Laplacian.laplacian w x - fderiv ℝ w x (b x))) :
    ∀ z, w z ≤ 2 * (L + p * (24 + 4 * n + 4 * B)) + (4 * p * C) ^ 2 + 2 * L + 1 := by
  intro z
  let r := unitCutoff z
  let F := fun x => r x ^ 2 * w x
  have hr : ContDiff ℝ 2 r := smooth_C2 (unitCutoff_smooth z)
  have hF : ContDiff ℝ 2 F := (hr.pow 2).mul hw
  have hz : z ∈ Metric.closedBall z (1 : ℝ) := by simp
  obtain ⟨x, hx, hmax⟩ := (isCompact_closedBall z (1 : ℝ)).exists_isMaxOn
    ⟨z, hz⟩ hF.continuous.continuousOn
  have hwx := hw0 x
  have hval : w z ≤ F x := by
    have H := hmax hz
    simpa [F,r,unitCutoff] using H
  by_cases hpz : w z ≤ 0
  · have hbound : 0 ≤ 2 * (L + p * (24 + 4 * n + 4 * B)) +
        (4 * p * C) ^ 2 + 2 * L + 1 := by positivity
    exact hpz.trans hbound
  have hpF : 0 < F x := lt_of_lt_of_le (lt_of_not_ge hpz) hval
  have hxn : ‖x - z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  have hr0 : 0 ≤ r x := by dsimp [r,unitCutoff]; nlinarith [norm_nonneg (x-z)]
  have hrx : 0 < r x := by
    have hn : r x ≠ 0 := by
      intro hzero
      have : F x = 0 := by simp [F,hzero]
      linarith
    exact lt_of_le_of_ne hr0 (Ne.symm hn)
  have hr1 : r x ≤ 1 := by dsimp [r,unitCutoff]; nlinarith [sq_nonneg ‖x-z‖]
  have hxi : x ∈ Metric.ball z (1 : ℝ) := by
    simp only [Metric.mem_ball, dist_eq_norm]
    dsimp [r,unitCutoff] at hrx
    nlinarith [norm_nonneg (x-z)]
  have hlocal : IsLocalMax F x := hmax.isLocalMax
    (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hxi) Metric.ball_subset_closedBall)
  have HC := cutoff_max_calculus hw hr hrx hlocal
  have hgn : ‖gradient r x‖ ≤ 2 := by
    change ‖gradient (unitCutoff z) x‖ ≤ 2
    rw [gradient_unitCutoff, norm_smul, Real.norm_eq_abs]
    norm_num
    linarith
  have hgn2 : ‖gradient r x‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (gradient r x)]
  have hLap : r x ^ 2 * Laplacian.laplacian w x ≤ (24 + 4 * n) * w x := by
    apply HC.1.trans
    apply mul_le_mul_of_nonneg_right _ (hw0 x)
    change 6 * ‖gradient r x‖ ^ 2 - 2 * r x * Laplacian.laplacian (unitCutoff z) x ≤ _
    rw [laplacian_unitCutoff]
    have H := mul_le_mul_of_nonneg_left hr1 (show (0 : ℝ) ≤ 4 * n by positivity)
    nlinarith
  have hDer : -(r x ^ 2) * fderiv ℝ w x (b x) ≤
      4 * r x * w x * (B + C * Real.sqrt (w x)) := by
    rw [HC.2]
    have hd : fderiv ℝ r x (b x) ≤ 2 * (B + C * Real.sqrt (w x)) := by
      rw [← inner_gradient_left]
      exact (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul hgn (hb x) (norm_nonneg _) (by norm_num)))
    have H := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * r x * w x by positivity)
    nlinarith
  exact hval.trans (cutoff_bernstein_algebra hrx hr1 (hw0 x) hL hp
    (by positivity) hB hC (heq x) hLap hDer)

def linearLogGradientBound (n : ℕ) (R : ℝ) : ℝ :=
  let N : ℝ := n + 1
  let L := 2 * R ^ 2 + N * R * n + 3 * N * R
  2 * (L + N * (24 + 4 * n)) + (8 * N) ^ 2 + 2 * L + 1

lemma log_gradient_bound_no_growth {n : ℕ} {h r : Space n → ℝ}
    (hh : ContDiff ℝ ∞ h) (hr : ContDiff ℝ ∞ r) {R : ℝ} (hR : 0 ≤ R)
    (heq : ∀ x, Laplacian.laplacian h x = r x - ‖gradient h x‖ ^ 2)
    (hrb : ∀ x, |r x| ≤ R) (hrd : ∀ i x, |coordDeriv r i x| ≤ R) :
    ∀ x, ‖gradient h x‖ ^ 2 ≤ linearLogGradientBound n R := by
  let N : ℝ := n + 1
  let L := 2 * R ^ 2 + N * R * n + 3 * N * R
  let w := fun x => ‖gradient h x‖ ^ 2
  let b := fun x => -(2 : ℝ) • gradient h x
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hL : 0 ≤ L := by dsimp [L,N]; positivity
  have hw : ContDiff ℝ 2 w := smooth_C2 (gradient_norm_sq_smooth hh)
  have hb : ∀ x, ‖b x‖ ≤ 0 + 2 * Real.sqrt (w x) := by
    intro x
    simp [b,w, norm_smul, Real.sqrt_sq (norm_nonneg (gradient h x))]
  have hP (x : Space n) : w x ^ 2 ≤ L * (1 + w x) +
      N * (Laplacian.laplacian w x - fderiv ℝ w x (b x)) := by
    let H := ∑ i : Fin n, ‖gradient (coordDeriv h i) x‖ ^ 2
    have hH : 0 ≤ H := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have htr := laplacian_sq_le_hessian hh x
    change Laplacian.laplacian h x ^ 2 ≤ n * H at htr
    have hr2 : r x ^ 2 ≤ R ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (r x)) (hrb x) 2
    have he := heq x
    change Laplacian.laplacian h x = r x - w x at he
    have hsq : w x ^ 2 ≤ 2 * R ^ 2 + 2 * N * H := by
      have hbasic : w x ^ 2 ≤ 2 * r x ^ 2 + 2 * Laplacian.laplacian h x ^ 2 := by
        rw [he]
        nlinarith [sq_nonneg (2 * r x - w x)]
      dsimp [N]
      nlinarith
    have hbo := log_bochner_lower (v := fun _ : Space n => 0)
      contDiff_const (fun _ => by constructor <;> norm_num) hh hr hR (le_refl (0 : ℝ))
      (fun y => by simpa [diffuseDrift] using heq y)
      (fun i y => (hrd i y).trans (by nlinarith [mul_nonneg hR (abs_nonneg (coordDeriv h i y))]))
      (fun i k y => by
        have hz : driftCoeff (fun _ : Space n => (0 : ℝ)) k = fun _ => 0 := by
          funext t; simp [driftCoeff]
        rw [hz]
        simp [coordDeriv]) x
    have hbo' : 2 * H ≤ Laplacian.laplacian w x - fderiv ℝ w x (b x) + R * n + 3 * R * w x := by
      have H' : 2 * H - R * n - 3 * R * w x ≤
          Laplacian.laplacian w x - fderiv ℝ w x (b x) := by
        simpa [H,w,b,diffuseDrift] using hbo
      linarith
    have hmul := mul_le_mul_of_nonneg_left hbo' hN
    have hlin : 2 * R ^ 2 + N * R * n + 3 * N * R * w x ≤ L * (1 + w x) := by
      have hw0 : 0 ≤ w x := sq_nonneg _
      have ha : 0 ≤ (2 * R ^ 2 + N * R * n) * w x := by positivity
      have hc : 0 ≤ 3 * N * R := by positivity
      dsimp [L]
      nlinarith
    nlinarith
  have HB := unbounded_bernstein_bound hw (fun x => sq_nonneg _) b hL hN
    (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2) hb hP
  intro x
  convert HB x using 1
  dsimp [linearLogGradientBound,L,N,w]
  ring

lemma linearLogGradientBound_nonneg (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ linearLogGradientBound n R := by
  dsimp [linearLogGradientBound]
  positivity

lemma positive_linear_log_gradient {n : ℕ} {f P : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hP : ContDiff ℝ ∞ P) (hp : ∀ x, 0 < f x)
    {R : ℝ} (hR : 0 ≤ R) (hPb : ∀ x, |P x| ≤ R)
    (hPd : ∀ i x, |coordDeriv P i x| ≤ R)
    (heq : ∀ x, Laplacian.laplacian f x = P x * f x) :
    ∀ x, ‖gradient (fun y => Real.log (f y)) x‖ ≤
      Real.sqrt (linearLogGradientBound n R) := by
  have hh : ContDiff ℝ ∞ (fun y => Real.log (f y)) := hf.log (fun x => (hp x).ne')
  have hlog (x : Space n) : Laplacian.laplacian (fun y => Real.log (f y)) x =
      P x - ‖gradient (fun y => Real.log (f y)) x‖ ^ 2 := by
    have H := drift_log (smooth_C2 hf) (fun y => (hp y).ne') (fun _ => 0) x
    simpa [heq x, (hp x).ne'] using H
  have H := log_gradient_bound_no_growth hh hP hR hlog hPb hPd
  intro x
  exact (Real.le_sqrt (norm_nonneg _) (linearLogGradientBound_nonneg n hR)).mpr (H x)

lemma positive_linear_log_lipschitz {n : ℕ} {f P : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hP : ContDiff ℝ ∞ P) (hp : ∀ x, 0 < f x)
    {R : ℝ} (hR : 0 ≤ R) (hPb : ∀ x, |P x| ≤ R)
    (hPd : ∀ i x, |coordDeriv P i x| ≤ R)
    (heq : ∀ x, Laplacian.laplacian f x = P x * f x) (x y : Space n) :
    |Real.log (f y) - Real.log (f x)| ≤
      Real.sqrt (linearLogGradientBound n R) * ‖y - x‖ := by
  have hh : ContDiff ℝ ∞ (fun y => Real.log (f y)) := hf.log (fun x => (hp x).ne')
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := Set.univ) (fun z _ => hh.differentiable (by simp) z)
    (fun z _ => show ‖fderiv ℝ (fun y => Real.log (f y)) z‖ ≤
        Real.sqrt (linearLogGradientBound n R) by
      simpa only [gradient, LinearIsometryEquiv.norm_map] using
        positive_linear_log_gradient hf hP hp hR hPb hPd heq z)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  exact H

lemma positive_linear_harnack {n : ℕ} {f P : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hP : ContDiff ℝ ∞ P) (hp : ∀ x, 0 < f x)
    {R : ℝ} (hR : 0 ≤ R) (hPb : ∀ x, |P x| ≤ R)
    (hPd : ∀ i x, |coordDeriv P i x| ≤ R)
    (heq : ∀ x, Laplacian.laplacian f x = P x * f x) (x y : Space n) :
    f y ≤ Real.exp (Real.sqrt (linearLogGradientBound n R) * ‖y - x‖) * f x := by
  have H := (abs_le.mp (positive_linear_log_lipschitz hf hP hp hR hPb hPd heq x y)).2
  have HH := Real.exp_le_exp.mpr H
  rw [Real.exp_sub, Real.exp_log (hp y), Real.exp_log (hp x)] at HH
  exact (div_le_iff₀ (hp x)).mp HH

lemma positive_linear_relative_gradient {n : ℕ} {f P : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hP : ContDiff ℝ ∞ P) (hp : ∀ x, 0 < f x)
    {R : ℝ} (hR : 0 ≤ R) (hPb : ∀ x, |P x| ≤ R)
    (hPd : ∀ i x, |coordDeriv P i x| ≤ R)
    (heq : ∀ x, Laplacian.laplacian f x = P x * f x) (x : Space n) :
    ‖gradient f x‖ ≤ Real.sqrt (linearLogGradientBound n R) * f x := by
  have H := positive_linear_log_gradient hf hP hp hR hPb hPd heq x
  rw [gradient_log (hf.differentiable (by simp) x) (hp x).ne', norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos (hp x)] at H
  have HH := mul_le_mul_of_nonneg_left H (hp x).le
  simpa [mul_assoc, (hp x).ne', mul_comm] using HH

end DeGiorgi
end

end OAI
