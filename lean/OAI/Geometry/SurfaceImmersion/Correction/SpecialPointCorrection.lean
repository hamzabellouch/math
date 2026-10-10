import Mathlib

namespace OAI

/-! Small affine bumps prescribe the vertical derivative near an isolated special point. -/
noncomputable section
open Filter Set Metric
open scoped ContDiff Topology

namespace ClosedSurfaceR4.TransverseSmallFunction

abbrev Base := ℝ × ℝ

def pointCorrection (p : Base) (φ : ContDiffBump p) (B : ℝ) (x : Base) : ℝ :=
  B * (x.2 - p.2) * φ x

lemma pointCorrection_smooth (p : Base) (φ : ContDiffBump p) (B : ℝ) :
    ContDiff ℝ ∞ (pointCorrection p φ B) :=
  (contDiff_const.mul (contDiff_snd.sub contDiff_const)).mul φ.contDiff

lemma pointCorrection_support (p : Base) (φ : ContDiffBump p) (B : ℝ) :
    tsupport (pointCorrection p φ B) ⊆ closedBall p φ.rOut := by
  rw [← φ.tsupport_eq]
  exact tsupport_mul_subset_right

lemma pointCorrection_compact (p : Base) (φ : ContDiffBump p) (B : ℝ) :
    HasCompactSupport (pointCorrection p φ B) := by
  exact φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
    (by rw [φ.tsupport_eq]; exact pointCorrection_support p φ B)

lemma pointCorrection_derivative {p x : Base} (φ : ContDiffBump p) (B : ℝ)
    (hx : x ∈ ball p φ.rIn) :
    fderiv ℝ (pointCorrection p φ B) x (0, 1) = B := by
  have he : pointCorrection p φ B =ᶠ[𝓝 x] (fun y : Base => B * (y.2 - p.2)) := by
    filter_upwards [φ.eventuallyEq_one_of_mem_ball hx] with y hy
    simp only [pointCorrection, hy, Pi.one_apply, mul_one]
  rw [he.fderiv_eq]
  have hd : HasFDerivAt (fun y : Base => B * (y.2 - p.2))
      (B • (ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    (hasFDerivAt_snd.sub_const p.2).const_mul B
  rw [hd.fderiv]
  simp

lemma pointCorrection_abs_le (p : Base) (φ : ContDiffBump p) (B : ℝ) (x : Base) :
    |pointCorrection p φ B x| ≤ |B| * φ.rOut := by
  by_cases hz : φ x = 0
  · simp only [pointCorrection, hz, mul_zero, abs_zero]
    exact mul_nonneg (abs_nonneg _) φ.rOut_pos.le
  have hmem : x ∈ ball p φ.rOut := by
    rw [← φ.support_eq]
    exact hz
  have hdist : dist x p < φ.rOut := hmem
  have hcoord : |x.2 - p.2| ≤ dist x p := by
    simpa only [dist_eq_norm, Prod.snd_sub, Real.norm_eq_abs] using norm_snd_le (x - p)
  have hφ : |φ x| ≤ 1 := by rw [abs_of_nonneg φ.nonneg]; exact φ.le_one
  calc
    |pointCorrection p φ B x| = |B| * |x.2 - p.2| * |φ x| := by simp only [pointCorrection, abs_mul]
    _ ≤ |B| * φ.rOut * 1 := mul_le_mul (mul_le_mul_of_nonneg_left
      (hcoord.trans hdist.le) (abs_nonneg B)) hφ (abs_nonneg _)
        (mul_nonneg (abs_nonneg B) φ.rOut_pos.le)
    _ = |B| * φ.rOut := mul_one _

theorem exists_special_point_correction {p : Base} {U : Set Base}
    (hU : IsOpen U) (hpU : p ∈ U) (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Base → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ U ∧
      (∀ x, |H x| < ε) ∧ ∃ V : Set Base, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
        ∀ x ∈ V, fderiv ℝ H x (0, 1) = B := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU p hpU
  let δ := min (r / 2) (ε / (|B| + 1))
  have hden : 0 < |B| + 1 := by positivity
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hε hden)
  have hδr : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let φ : ContDiffBump p := ⟨δ / 2, δ, by positivity, by linarith⟩
  have hball : closedBall p δ ⊆ U := by
    intro x hx
    exact hrU ((mem_ball).mpr (lt_of_le_of_lt hx hδr))
  have hsmall : |B| * δ < ε := by
    have hb : |B| * (ε / (|B| + 1)) < ε := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hden).mpr
      nlinarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg B)) hb
  refine ⟨pointCorrection p φ B, pointCorrection_smooth p φ B,
    pointCorrection_compact p φ B, (pointCorrection_support p φ B).trans hball,
    (fun x => lt_of_le_of_lt (pointCorrection_abs_le p φ B x) hsmall),
    ball p φ.rIn, isOpen_ball, mem_ball_self φ.rIn_pos, ?_, ?_⟩
  · exact (ball_subset_closedBall.trans (closedBall_subset_closedBall φ.rIn_lt_rOut.le)).trans hball
  · exact fun x hx => pointCorrection_derivative φ B hx

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
