import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszPole
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTZetaGrowth
import OAI.NumberTheory.TwoPoint.Fourier.ModFiveVerticalTails

namespace OAI

/-! Integrability and the far tails of the shifted quadratic Riesz integral. -/

namespace TwoPointCorrelations

open Complex Set MeasureTheory _root_.Erdos970 _root_.OAI.Erdos970

lemma mrt_zeta_riesz_integrable {x b : ℝ} (hx : 0 < x) (hb : 1 < b) (u : ℝ) :
    Integrable (fun t : ℝ => mrtZetaRieszIntegrand x u ((b : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨C, hC, hr⟩ := mrt_zeta_logderiv_right_bound
  have hB : 0 ≤ 1 / (b - 1) + C := by positivity
  have hc : Continuous (fun t : ℝ => mrtZetaRieszIntegrand x u ((b : ℂ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    let s : ℂ := (b : ℂ) + (t : ℂ) * Complex.I
    let z : ℂ := s + (u : ℂ) * Complex.I
    have hzr : 1 < z.re := by simpa [z, s] using hb
    have hz1 : z ≠ 1 := by intro he; rw [he] at hzr; norm_num at hzr
    have hline : ContinuousAt (fun t : ℝ => (b : ℂ) + (t : ℂ) * Complex.I) t := by fun_prop
    have hadd : ContinuousAt (fun t : ℝ => (b : ℂ) + (t : ℂ) * Complex.I +
        (u : ℂ) * Complex.I) t := by fun_prop
    have hg := (((analyticOn_riemannZeta z hz1).deriv.continuousAt.neg.div
      (differentiableAt_riemannZeta hz1).continuousAt
      (riemannZeta_ne_zero_of_one_le_re hzr.le)).comp
        (f := fun t : ℝ => (b : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) hadd)
    have hk := (mrt_riesz_kernel_differentiableAt hx (s := s)
      (by intro he; have hh := congrArg Complex.re he; norm_num [s] at hh; linarith)
      (by intro he; have hh := congrArg Complex.re he; norm_num [s] at hh; linarith)
      (by intro he; have hh := congrArg Complex.re he; norm_num [s] at hh; linarith)).continuousAt.comp
        (f := fun t : ℝ => (b : ℂ) + (t : ℂ) * Complex.I) hline
    exact hg.mul hk
  have hm : Integrable (fun t : ℝ =>
      ((1 / (b - 1) + C) * (4 * x ^ b)) / (1 + t ^ 2)) := by
    simpa only [div_eq_mul_inv] using
      integrable_inv_one_add_sq.const_mul ((1 / (b - 1) + C) * (4 * x ^ b))
  apply hm.mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  have hh := hr (b - 1) (t + u) (by linarith)
  have heq : (((1 + (b - 1) : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) =
      (b : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I := by push_cast; ring
  rw [heq] at hh
  rw [mrtZetaRieszIntegrand, norm_mul, neg_div, norm_neg]
  exact (mul_le_mul hh (mrt_riesz_kernel_vertical hx (by linarith) t)
    (norm_nonneg _) hB).trans_eq (by ring)

lemma mrt_vertical_power_tails {f : ℂ → ℂ} {b T D a : ℝ}
    (hT : 0 < T) (ha : 1 < a)
    (hf : Integrable (fun t : ℝ => f ((b : ℂ) + (t : ℂ) * Complex.I)))
    (hbound : ∀ t : ℝ, T ≤ |t| →
      ‖f ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D * |t| ^ (-a)) :
    ‖VerticalIntegral f b - VIntegral f b (-T) T‖ ≤
      2 * D * T ^ (1 - a) / (a - 1) := by
  have hu : ‖∫ t in Ioi T, f ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * T ^ (1 - a) / (a - 1) := by
    apply mrt_power_integral_tail hT ha
    intro t ht
    simpa only [abs_of_pos (hT.trans ht)] using hbound t
      (by rw [abs_of_pos (hT.trans ht)]; exact ht.le)
  have hd : ‖∫ t in Iic (-T), f ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * T ^ (1 - a) / (a - 1) := by
    rw [← integral_comp_neg_Ioi T]
    apply mrt_power_integral_tail hT ha
    intro t ht
    simpa only [abs_neg, abs_of_pos (hT.trans ht)] using hbound (-t)
      (by rw [abs_neg, abs_of_pos (hT.trans ht)]; exact ht.le)
  rw [verticalIntegral_split_three (-T) T hf]
  have he (x y z : ℂ) : x + y + z - y = x + z := by ring
  rw [he]
  calc
    _ ≤ ‖Complex.I • (∫ t in Iic (-T), f ((b : ℂ) + (t : ℂ) * Complex.I))‖ +
        ‖Complex.I • (∫ t in Ici T, f ((b : ℂ) + (t : ℂ) * Complex.I))‖ := norm_add_le _ _
    _ = ‖∫ t in Iic (-T), f ((b : ℂ) + (t : ℂ) * Complex.I)‖ +
        ‖∫ t in Ioi T, f ((b : ℂ) + (t : ℂ) * Complex.I)‖ := by
      rw [norm_smul, norm_smul, norm_I, one_mul, one_mul, integral_Ici_eq_integral_Ioi]
    _ ≤ D * T ^ (1 - a) / (a - 1) + D * T ^ (1 - a) / (a - 1) := add_le_add hd hu
    _ = _ := by ring

lemma mrt_shifted_log_height {t u : ℝ} (ht : Real.exp 1 ≤ |t|) (hu : |u| ≤ |t| / 2) :
    mrtVKLog (2 * (t + u)) ≤ 6 * Real.log |t| := by
  have ht0 : 0 < |t| := (Real.exp_pos _).trans_le ht
  have ht1 : 1 ≤ |t| := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog : 1 ≤ Real.log |t| := (Real.le_log_iff_exp_le ht0).mpr ht
  have hh : |2 * (t + u)| + 3 ≤ 6 * |t| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := abs_add_le t u
    linarith
  have hl := Real.log_le_log (by positivity : 0 < |2 * (t + u)| + 3) hh
  rw [Real.log_mul (by norm_num) ht0.ne'] at hl
  have h6 : Real.log 6 ≤ 5 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num)
    linarith
  change Real.log (|2 * (t + u)| + 3) ≤ 6 * Real.log |t|
  linarith

/-- The constant has deliberately ample room; the essential saving is T^-3/2,
which can be charged to the pole term even for arbitrarily large cutoffs x. -/
theorem MRTWeakHurwitzGrowthInput.riesz_far_tail (h : MRTWeakHurwitzGrowthInput) :
    ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧ ∀ x b T u : ℝ,
      0 < x → 1 < b → T₀ ≤ T → |u| ≤ T / 2 →
        ‖VerticalIntegral (mrtZetaRieszIntegrand x u) b -
          VIntegral (mrtZetaRieszIntegrand x u) b (-T) T‖ ≤
            C * x ^ b * T ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C, T₁, hC, hT₁, hg⟩ := h.zeta_right_growth
  refine ⟨1536 * C, max (2 * T₁) (Real.exp 1), by positivity,
    lt_of_lt_of_le (by positivity : 0 < 2 * T₁) (le_max_left _ _), ?_⟩
  intro x b T u hx hb hT hu
  have hT1 : 2 * T₁ ≤ T := (le_max_left _ _).trans hT
  have hTe : Real.exp 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := (Real.exp_pos _).trans_le hTe
  have htbound : ∀ t : ℝ, T ≤ |t| →
      ‖mrtZetaRieszIntegrand x u ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (1152 * C * x ^ b) * |t| ^ (-(5 / 2 : ℝ)) := by
    intro t ht
    have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
    have htu : T₁ ≤ |t + u| := by
      have hh := abs_add_le (t + u) (-u)
      rw [add_neg_cancel_right, abs_neg] at hh
      linarith
    have hh := hg b (t + u) htu hb
    have heq : (b : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I =
        (b : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I := by push_cast; ring
    rw [heq] at hh
    have hlog := mrt_shifted_log_height (hTe.trans ht) (hu.trans (by linarith))
    have hl : Real.log |t| ≤ 4 * |t| ^ (1 / 4 : ℝ) := by
      have hz := Real.log_le_rpow_div (abs_nonneg t) (by norm_num : (0 : ℝ) < 1 / 4)
      linarith
    have hH0 := (mrt_VKLog_pos (2 * (t + u))).le
    have hlog0 : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])
    have hp : (mrtVKLog (2 * (t + u))) ^ 2 ≤ 576 * |t| ^ (1 / 2 : ℝ) := by
      have he : (|t| ^ (1 / 4 : ℝ)) ^ 2 = |t| ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg t)]
        congr 1
        norm_num
      nlinarith [sq_nonneg (6 * Real.log |t| - mrtVKLog (2 * (t + u))),
        sq_nonneg (4 * |t| ^ (1 / 4 : ℝ) - Real.log |t|)]
    rw [mrtZetaRieszIntegrand, norm_mul, neg_div, norm_neg]
    apply (mul_le_mul (hh.trans (mul_le_mul_of_nonneg_left hp hC.le))
      (mrt_riesz_kernel_cubic hx b ht0) (norm_nonneg _) (by positivity)).trans_eq
    have htpos := abs_pos.mpr ht0
    have hid : |t| ^ (1 / 2 : ℝ) / |t| ^ (3 : ℕ) = |t| ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_sub htpos]
      congr 1
      norm_num
    calc
      _ = (1152 * C * x ^ b) * (|t| ^ (1 / 2 : ℝ) / |t| ^ (3 : ℕ)) := by ring
      _ = _ := by rw [hid]
  have hh := mrt_vertical_power_tails hT0 (by norm_num : (1 : ℝ) < 5 / 2)
    (mrt_zeta_riesz_integrable hx hb u) htbound
  convert hh using 1
  norm_num
  ring

end TwoPointCorrelations

end OAI
