import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingEstimates

namespace OAI

/-! # The outgoing Robin error in logarithmic radius

The normalized first derivatives decay like `exp (-2t)`. The equal-modulus
physical diagonal transfers that decay to the full two-channel Robin map.
-/

open Set Filter Topology

namespace DefocusingNLS

local notation "V" => ℂ × ℂ

noncomputable def homogeneousPhysicalLogDerivativeColumn (νp νm : ℂ)
    (f g : ℝ → ℂ) (t : ℝ) : V :=
  homogeneousDiagonal (Complex.exp (νp * (t : ℂ))) (Complex.exp (νm * (t : ℂ)))
    (homogeneousDiagonal νp νm (f t, g t) + (deriv f t, deriv g t))

theorem homogeneousPhysicalLogDerivativeColumn_hasDerivAt (νp νm : ℂ)
    (f g : ℝ → ℂ) (t : ℝ) (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    HasDerivAt (homogeneousPhysicalLogColumn νp νm f g)
      (homogeneousPhysicalLogDerivativeColumn νp νm f g t) t := by
  have hp := ((hasDerivAt_id t).ofReal_comp.const_mul νp).cexp
  have hm := ((hasDerivAt_id t).ofReal_comp.const_mul νm).cexp
  simp only [id_eq, Complex.ofReal_one, mul_one] at hp hm
  apply ((hp.mul hf.hasDerivAt).prodMk (hm.mul hg.hasDerivAt)).congr_deriv
  apply Prod.ext
  all_goals
    simp only [homogeneousPhysicalLogDerivativeColumn, homogeneousDiagonal_apply,
      Prod.fst_add, Prod.snd_add]
    ring

private theorem norm_pair_le_sum (u v : ℂ) : ‖(u, v)‖ ≤ ‖u‖ + ‖v‖ := by
  rw [Prod.norm_def]
  exact max_le (by linarith [norm_nonneg v]) (by linarith [norm_nonneg u])

theorem homogeneousOutgoingRobin_error (νp νm : ℂ) (hν : νp.re = νm.re)
    (fp gp fm gm : ℝ → ℂ)
    (hp : Tendsto (fun t => (fp t, gp t)) atTop (𝓝 (1, 0)))
    (hm : Tendsto (fun t => (fm t, gm t)) atTop (𝓝 (0, 1)))
    (hfp : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop, ‖deriv fp t‖ ≤ A * Real.exp (-2 * t))
    (hgp : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop, ‖deriv gp t‖ ≤ A * Real.exp (-2 * t))
    (hfm : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop, ‖deriv fm t‖ ≤ A * Real.exp (-2 * t))
    (hgm : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop, ‖deriv gm t‖ ≤ A * Real.exp (-2 * t)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ t in atTop,
      ‖spectralRobinOperator (homogeneousPhysicalLogColumn νp νm fp gp t)
          (homogeneousPhysicalLogColumn νp νm fm gm t)
          (homogeneousPhysicalLogDerivativeColumn νp νm fp gp t)
          (homogeneousPhysicalLogDerivativeColumn νp νm fm gm t) -
        homogeneousDiagonal νp νm‖ ≤ M * Real.exp (-2 * t) := by
  obtain ⟨J, hJ, hInv⟩ := homogeneousNormalizedInverse_bound _ _ hp hm
  obtain ⟨A, hA, ha⟩ := hfp
  obtain ⟨B, hB, hb⟩ := hgp
  obtain ⟨C, hC, hc⟩ := hfm
  obtain ⟨D, hD, hd⟩ := hgm
  refine ⟨(A + B + C + D) * J, by positivity, ?_⟩
  filter_upwards [hInv, ha, hb, hc, hd] with t hi htA htB htC htD
  have hnormp : ‖Complex.exp (νp * (t : ℂ))‖ = Real.exp (νp.re * t) := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  have hnormm : ‖Complex.exp (νm * (t : ℂ))‖ = Real.exp (νp.re * t) := by
    simpa only [hν] using (show ‖Complex.exp (νm * (t : ℂ))‖ = Real.exp (νm.re * t) by
      simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero])
  have hpair : ‖(deriv fp t, deriv gp t)‖ + ‖(deriv fm t, deriv gm t)‖ ≤
      (A + B + C + D) * Real.exp (-2 * t) := by
    calc
      _ ≤ (‖deriv fp t‖ + ‖deriv gp t‖) + (‖deriv fm t‖ + ‖deriv gm t‖) :=
        add_le_add (norm_pair_le_sum _ _) (norm_pair_le_sum _ _)
      _ ≤ (A * Real.exp (-2 * t) + B * Real.exp (-2 * t)) +
          (C * Real.exp (-2 * t) + D * Real.exp (-2 * t)) :=
        add_le_add (add_le_add htA htB) (add_le_add htC htD)
      _ = _ := by ring
  have hh := homogeneousDiagonal_robin_bound _ _ (Real.exp (νp.re * t)) (Real.exp_pos _)
    hnormp hnormm (fp t, gp t) (fm t, gm t) (deriv fp t, deriv gp t) (deriv fm t, deriv gm t)
    hi.1 (homogeneousDiagonal νp νm) (homogeneousDiagonal_commute _ _ _ _)
  simp only [homogeneousPhysicalLogColumn_diagonal, homogeneousPhysicalLogDerivativeColumn]
  apply hh.trans
  have h := mul_le_mul hpair hi.2 (norm_nonneg _)
    (show 0 ≤ (A + B + C + D) * Real.exp (-2 * t) by positivity)
  convert h using 1
  ring

theorem homogeneousLogRobin_error_to_radial
    (A : ℝ → V →L[ℂ] V) (K : V →L[ℂ] V) (M : ℝ)
    (hA : ∀ᶠ t in atTop, ‖A t - K‖ ≤ M * Real.exp (-2 * t)) :
    ∀ᶠ r : ℝ in atTop,
      ‖r⁻¹ • A (Real.log r) - r⁻¹ • K‖ ≤ M / r ^ (3 : ℕ) := by
  filter_upwards [Real.tendsto_log_atTop.eventually hA,
    eventually_gt_atTop (0 : ℝ)] with r hAr hr
  rw [← smul_sub (r⁻¹ : ℝ) (A (Real.log r)) K,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  apply (mul_le_mul_of_nonneg_left hAr (inv_nonneg.mpr hr.le)).trans_eq
  have he : Real.exp (-2 * Real.log r) = (r * r)⁻¹ := by
    rw [neg_mul, Real.exp_neg, two_mul, Real.exp_add, Real.exp_log hr]
  rw [he]
  field_simp [hr.ne']

end DefocusingNLS

end OAI
