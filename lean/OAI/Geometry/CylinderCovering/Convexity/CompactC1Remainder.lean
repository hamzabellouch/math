import Mathlib

namespace OAI

noncomputable section
open Set Metric
namespace CylinderCovering

theorem compact_c1_remainder
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : E → F} (hf : ContDiffOn ℝ 1 f U)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ K, ball p r ⊆ U ∧
      ∀ q ∈ ball p r,
        ‖f q - f p - fderiv ℝ f p (q-p)‖ ≤ eps * ‖q-p‖ := by
  obtain ⟨a, ha, haU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hKa : IsCompact (cthickening a K) := hK.cthickening
  have hder : ContinuousOn (fderiv ℝ f) (cthickening a K) := by
    intro p hp
    exact ((hf.contDiffAt (hU.mem_nhds (haU hp))).continuousAt_fderiv
      (by norm_num)).continuousWithinAt
  have huc := hKa.uniformContinuousOn_of_continuous hder
  obtain ⟨d, hd, hdist⟩ := Metric.uniformContinuousOn_iff.mp huc eps heps
  let r := min a d / 2
  have hr : 0 < r := half_pos (lt_min ha hd)
  have hra : r < a := by dsimp [r]; linarith [min_le_left a d]
  have hrd : r < d := by dsimp [r]; linarith [min_le_right a d]
  have hnear : ∀ p ∈ K, ball p r ⊆ cthickening a K := by
    intro p hp q hq
    apply thickening_subset_cthickening a K
    apply mem_thickening_iff.mpr
    exact ⟨p, hp, (mem_ball.mp hq).trans hra⟩
  refine ⟨r, hr, ?_⟩
  intro p hp
  have hballU : ball p r ⊆ U := (hnear p hp).trans haU
  refine ⟨hballU, ?_⟩
  intro q hq
  apply (convex_ball p r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (φ := fderiv ℝ f p)
    (fun z hz => ((hf.contDiffAt (hU.mem_nhds (hballU hz))).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => ?_) (mem_ball_self hr) hq
  have hh := hdist z (hnear p hp hz) p (self_subset_cthickening K hp)
    ((mem_ball.mp hz).trans hrd)
  simpa only [dist_eq_norm] using hh.le

theorem compact_positive_weight_ratio
    {E : Type*} [PseudoMetricSpace E] {K : Set E} (hK : IsCompact K)
    {j : E → ℝ} (hj : ContinuousOn j K) (hjpos : ∀ p ∈ K, 0 < j p)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ K, ∀ q ∈ K, dist p q < r →
      j p ≤ (1+eta) * j q := by
  by_cases hne : K.Nonempty
  · obtain ⟨p0, hp0, hmin⟩ := hK.exists_isMinOn hne hj
    have hsmall : 0 < eta * j p0 := mul_pos heta (hjpos p0 hp0)
    obtain ⟨r, hr, hdist⟩ := Metric.uniformContinuousOn_iff.mp
      (hK.uniformContinuousOn_of_continuous hj) (eta*j p0) hsmall
    refine ⟨r, hr, ?_⟩
    intro p hp q hq hpq
    have hc := hdist p hp q hq hpq
    rw [Real.dist_eq] at hc
    have hm : j p0 ≤ j q := hmin hq
    have hv := le_abs_self (j p-j q)
    nlinarith
  · exact ⟨1, zero_lt_one, fun p hp => (hne ⟨p,hp⟩).elim⟩

end CylinderCovering

end

end OAI
