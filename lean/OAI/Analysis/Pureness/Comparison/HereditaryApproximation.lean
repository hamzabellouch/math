import OAI.Analysis.Pureness.Comparison.SupportApproximation
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI
open Filter Topology
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma supportCutoff_mul_error (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |supportCutoff n t * t - t| ≤ 1 / ((n : ℝ) + 1) := by
  have hk : 0 < (n : ℝ) + 1 := by positivity
  unfold supportCutoff
  rw [max_eq_left ht]
  by_cases h : ((n : ℝ) + 1) * t ≤ 1
  · rw [min_eq_left h, abs_of_nonpos (by nlinarith)]
    have ht' : t ≤ 1 / ((n : ℝ) + 1) := (le_div_iff₀ hk).mpr (by nlinarith)
    nlinarith [sq_nonneg t]
  · rw [min_eq_right (le_of_not_ge h)]
    simp
    positivity

lemma supportApprox_mul_self_error {b : A} (hb : 0 ≤ b) (n : ℕ) :
    ‖supportApprox b n * b - b‖ ≤ 1 / ((n : ℝ) + 1) := by
  have heq : cfc (fun t : ℝ => supportCutoff n t * t - t) b = supportApprox b n * b - b := by
    rw [cfc_sub (fun t : ℝ => supportCutoff n t * t) (fun t : ℝ => t) b ((supportCutoff_continuous n).mul continuous_id).continuousOn continuousOn_id,
      cfc_mul (supportCutoff n) (fun t : ℝ => t) b (supportCutoff_continuous n).continuousOn continuousOn_id, cfc_id' ℝ b]
    rfl
  rw [← heq]
  apply norm_cfc_le (by positivity)
  intro t ht
  exact supportCutoff_mul_error n (spectrum_nonneg_of_nonneg hb ht)

lemma supportApprox_mul_self_tendsto {b : A} (hb : 0 ≤ b) :
    Tendsto (fun n => supportApprox b n * b) atTop (𝓝 b) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (supportApprox_mul_self_error hb)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem supportApprox_mul_tendsto {b x : A} (hb : 0 ≤ b)
    (hx : x ∈ hereditaryCorner b hb) :
    Tendsto (fun n => supportApprox b n * x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 4) (by positivity)
  obtain ⟨c, rfl⟩ := hy
  let y := b * c * b
  have hyt : Tendsto (fun n => supportApprox b n * y) atTop (𝓝 y) := by
    simpa only [y, mul_assoc] using ((supportApprox_mul_self_tendsto hb).mul_const c).mul_const b
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hyt (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have heq : supportApprox b n * x - x =
      supportApprox b n * (x - y) + (supportApprox b n * y - y) + (y - x) := by
    simp only [mul_sub]
    abel
  have h1 : ‖supportApprox b n * (x - y)‖ ≤ ‖x - y‖ := by
    exact (norm_mul_le _ _).trans (by
      have h := supportApprox_norm_le_one b n
      nlinarith [norm_nonneg (x - y)])
  have h2 : ‖supportApprox b n * y - y‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hN n hn
  have h3 : ‖x - y‖ < ε / 4 := by simpa only [dist_eq_norm, y] using hxy
  rw [dist_eq_norm, heq]
  have h4 := norm_add_le (supportApprox b n * (x - y) + (supportApprox b n * y - y)) (y - x)
  have h5 := norm_add_le (supportApprox b n * (x - y)) (supportApprox b n * y - y)
  rw [norm_sub_rev y x] at h4
  linarith

theorem mul_supportApprox_tendsto {b x : A} (hb : 0 ≤ b)
    (hx : x ∈ hereditaryCorner b hb) :
    Tendsto (fun n => x * supportApprox b n) atTop (𝓝 x) := by
  have h := (supportApprox_mul_tendsto hb ((hereditaryCorner b hb).star_mem' hx)).star
  simpa only [star_mul, star_star, fun n => (supportApprox_nonneg b n).star_eq] using h
end CuntzComparison

end OAI
