import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactWeakConvergence

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter Topology
open scoped CompactlySupported ENNReal

theorem compactTest_integral_difference_bound {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f g : C_c(Ambient d, ℝ)) (S : Set (Ambient d))
    (hfin : μ S < ∞) (hzero : ∀ x, x ∉ S → f x = 0 ∧ g x = 0)
    (δ : ℝ) (hdiff : ∀ x, |f x - g x| ≤ δ) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤ δ * μ.real S := by
  have hf : Integrable (fun x => f x) μ :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hg : Integrable (fun x => g x) μ :=
    g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  rw [← integral_sub hf hg]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
    (fun x hx => by rw [(hzero x hx).1, (hzero x hx).2, sub_self])]
  simpa only [Real.norm_eq_abs] using! norm_setIntegral_le_of_norm_le_const
    (f := fun x => f x - g x) (C := δ) hfin
    (fun x _ => by simpa only [Real.norm_eq_abs] using! hdiff x)

theorem compactTestConvergence_varying_tests {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] (hlocal : CompactTestConvergence μ ν)
    (f : ℕ → C_c(Ambient d, ℝ)) (g : C_c(Ambient d, ℝ))
    (S : Set (Ambient d)) (M : ℝ) (hM : 0 ≤ M)
    (hsupport : ∀ᶠ j in atTop, (μ j) S < ∞ ∧ (μ j).real S ≤ M ∧
      ∀ x, x ∉ S → f j x = 0 ∧ g x = 0)
    (huniform : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x, |f j x - g x| < ε) :
    Tendsto (fun j => ∫ x, f j x ∂μ j) atTop (𝓝 (∫ x, g x ∂ν)) := by
  have hdiff : Tendsto (fun j => (∫ x, f j x ∂μ j) - ∫ x, g x ∂μ j) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hMp : 0 < M + 1 := by linarith
    let δ := ε / (M + 1)
    have hδ : 0 < δ := div_pos hε hMp
    have hδM : δ * M < ε := by
      have heq : δ * (M + 1) = ε := div_mul_cancel₀ ε hMp.ne'
      nlinarith
    filter_upwards [hsupport, huniform δ hδ] with j hj hfj
    have hb := compactTest_integral_difference_bound (μ j) (f j) g S hj.1 hj.2.2 δ
      (fun x => (hfj x).le)
    have hbound := hb.trans (mul_le_mul_of_nonneg_left hj.2.1 hδ.le)
    simpa only [Real.dist_eq, sub_zero] using! hbound.trans_lt hδM
  have ht := hdiff.add (hlocal g)
  simpa only [sub_add_cancel, zero_add] using! ht

end

end RieszRectifiability

end OAI
