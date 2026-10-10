import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEulerPhysical
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingLogJets

namespace OAI

/-! Actual physical derivatives of a bounded normalized outgoing column. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
local notation "V" => ℂ × ℂ

theorem homogeneousGlued_euler_congr (F G : ℝ → V) (t : ℝ)
    (he : F =ᶠ[𝓝 t] G) (N : ℕ) :
    homogeneousEulerDeriv F N t = homogeneousEulerDeriv G N t := by
  have hh : ∀ n : ℕ, homogeneousEulerDeriv F n =ᶠ[𝓝 t] homogeneousEulerDeriv G n := by
    intro n
    induction n with
    | zero => exact he
    | succ n ih =>
      filter_upwards [ih.deriv, ih] with s hds hs
      change deriv (homogeneousEulerDeriv F n) s - (n : ℝ) • homogeneousEulerDeriv F n s = _
      rw [hds, hs]
      rfl
  exact (hh N).eq_of_nhds

theorem homogeneousGlued_physical_derivative_bound
    (νp νm : ℂ) (σ : ℝ) (hp : νp.re = σ) (hm : νm.re = σ)
    (U : ℝ → V) (hU : ContDiffOn ℝ ∞ U (Ioi 0))
    (f g : ℝ → ℂ) (hf : HasLogJetBound 0 f) (hg : HasLogJetBound 0 g)
    (L : ℝ) (he : ∀ t, L < t → U (Real.exp t) =
      (Complex.exp (νp * (t : ℂ)) * f t, Complex.exp (νm * (t : ℂ)) * g t))
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in atTop,
      ‖iteratedDeriv N U r‖ ≤ C * r ^ (σ - (N : ℝ)) := by
  obtain ⟨Lf, hfs⟩ := hf.smooth
  obtain ⟨Lg, hgs⟩ := hg.smooth
  let K := max L (max Lf Lg)
  have hfs' := hfs.mono (Ioi_subset_Ioi ((le_max_left Lf Lg).trans (le_max_right L _)))
  have hgs' := hgs.mono (Ioi_subset_Ioi ((le_max_right Lf Lg).trans (le_max_right L _)))
  obtain ⟨A, hA, hAf⟩ := (homogeneousNormalizedEuler_bound νp f hf N).bound 0
  obtain ⟨B, _hB, hBg⟩ := (homogeneousNormalizedEuler_bound νm g hg N).bound 0
  simp only [iteratedDeriv_zero, zero_mul, Real.exp_zero, mul_one] at hAf hBg
  have hbound : ∀ᶠ t : ℝ in atTop,
      ‖iteratedDeriv N U (Real.exp t)‖ ≤ max A B * Real.exp ((σ - (N : ℝ)) * t) := by
    filter_upwards [hAf, hBg, eventually_gt_atTop K] with t htA htB htK
    have hevent : (fun s => U (Real.exp s)) =ᶠ[𝓝 t]
        (fun s => (Complex.exp (νp * (s : ℂ)) * f s,
          Complex.exp (νm * (s : ℂ)) * g s)) := by
      filter_upwards [Ioi_mem_nhds ((le_max_left L (max Lf Lg)).trans_lt htK)] with s hs
      exact he s hs
    have hid := homogeneousGlued_euler_congr _ _ t hevent N
    rw [homogeneousEulerDeriv_physical U hU N t,
      homogeneousEulerDeriv_normalized νp νm f g K hfs' hgs' N t htK] at hid
    have hn : ‖Real.exp ((N : ℝ) * t) • iteratedDeriv N U (Real.exp t)‖ ≤
        max A B * Real.exp (σ * t) := by
      rw [hid, Prod.norm_def]
      apply max_le
      · rw [norm_mul, Complex.norm_exp]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
          sub_zero, hp]
        calc
          _ ≤ Real.exp (σ * t) * A := mul_le_mul_of_nonneg_left htA (Real.exp_pos _).le
          _ = A * Real.exp (σ * t) := mul_comm _ _
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left A B) (Real.exp_pos _).le
      · rw [norm_mul, Complex.norm_exp]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
          sub_zero, hm]
        calc
          _ ≤ Real.exp (σ * t) * B := mul_le_mul_of_nonneg_left htB (Real.exp_pos _).le
          _ = B * Real.exp (σ * t) := mul_comm _ _
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right A B) (Real.exp_pos _).le
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
    apply (mul_le_mul_iff_right₀ (Real.exp_pos ((N : ℝ) * t))).mp
    have hExp : Real.exp (σ * t) =
        Real.exp ((σ - (N : ℝ)) * t) * Real.exp ((N : ℝ) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hExp] at hn
    nlinarith
  refine ⟨max A B, hA.trans (le_max_left _ _), ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hbound,
    eventually_gt_atTop (0 : ℝ)] with r hr hr0
  rw [Real.exp_log hr0] at hr
  simpa only [Real.rpow_def_of_pos hr0, mul_comm] using hr

end DefocusingNLS

end OAI
