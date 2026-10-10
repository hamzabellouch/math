import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledProfiles

namespace OAI

/-! # Sublinear sheet distance forces equality of limiting profiles -/

namespace PolycyclicRecognition

open Filter
open scoped Topology NNReal

variable {G W Z : Type*} [Group G] [PseudoMetricSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- This compares the actual two suffixes with the same center and chart.
Only their source distance at the chosen chart point must be sublinear. -/
theorem rescaled_profile_limits_eq_of_sublinear_sheet_distance
    {K : ℝ≥0} (J : ℕ → G → W) (hJ : ∀ n, LipschitzWith K (J n))
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (x k l : ℕ → G) (chart : ℕ → Z → G) (z : ℕ → Z) (f g : W)
    (hf : Tendsto (fun n => rescaledMapProfile (J n) (x n) (k n)
      (Real.log (scale n)) (chart n) (z n)) atTop (𝓝 f))
    (hg : Tendsto (fun n => rescaledMapProfile (J n) (x n) (l n)
      (Real.log (scale n)) (chart n) (z n)) atTop (𝓝 g))
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      dist (x n * k n * chart n (z n)) (x n * l n * chart n (z n)) ≤ ε * scale n) :
    f = g := by
  have hb (ε : ℝ) (hε : 0 < ε) : dist f g ≤ (K : ℝ) * ε := by
    apply le_of_tendsto (hf.dist hg)
    filter_upwards [hnear ε hε] with n hn
    have he : dist
        (rescaledMapProfile (J n) (x n) (k n) (Real.log (scale n)) (chart n) (z n))
        (rescaledMapProfile (J n) (x n) (l n) (Real.log (scale n)) (chart n) (z n)) =
        (scale n)⁻¹ * dist (J n (x n * k n * chart n (z n)))
          (J n (x n * l n * chart n (z n))) := by
      simp only [rescaledMapProfile, dist_eq_norm, ← smul_sub,
        sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_inv,
        Real.exp_log (hscale n), abs_of_pos (hscale n)]
    rw [he]
    calc
      _ ≤ (scale n)⁻¹ * ((K : ℝ) *
          dist (x n * k n * chart n (z n)) (x n * l n * chart n (z n))) :=
        mul_le_mul_of_nonneg_left ((hJ n).dist_le_mul _ _) (inv_nonneg.mpr (hscale n).le)
      _ ≤ (scale n)⁻¹ * ((K : ℝ) * (ε * scale n)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn K.coe_nonneg)
          (inv_nonneg.mpr (hscale n).le)
      _ = (K : ℝ) * ε := by field_simp [(hscale n).ne']
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < (K : ℝ) + 1 := by positivity
  have hh := hb (ε / ((K : ℝ) + 1)) (div_pos hε hden)
  have hquot : (K : ℝ) * (ε / ((K : ℝ) + 1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  simpa only [zero_add] using hh.trans hquot

end PolycyclicRecognition

end OAI
