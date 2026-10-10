import OAI.Probability.SLE.Loewner.SmoothRawTraceContinuity
import OAI.Probability.SLE.Loewner.SmoothRawTraceBounds
import OAI.Probability.SLE.Loewner.SmoothDriverLipschitz

namespace OAI

/-! Smooth drivers with bounded derivative generate a continuous raw tip
at all nonnegative times, including the initial boundary point. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

lemma smooth_trace_zero (b : Driver) (b' : ℝ → ℝ) (L : ℝ≥0)
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt (driverValue b) (b' t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → |b' t| ≤ L) : trace 1 b 0=0 := by
  have hh := smooth_raw_trace_position_bounds b 0 b'
    (fun t ht => (hd t ht.1).mono Icc_subset_Ici_self) L.coe_nonneg (fun t ht => hb t ht.1)
  simp only [NNReal.coe_zero,mul_zero] at hh
  apply Complex.ext
  · simpa only [Complex.zero_re] using abs_nonpos_iff.mp hh.1
  · simpa only [Complex.zero_im] using (show (trace 1 b 0).im=0 by nlinarith [sq_nonneg (trace 1 b 0).im])

lemma smooth_trace_norm_le (b : Driver) (b' : ℝ → ℝ) (L : ℝ≥0)
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt (driverValue b) (b' t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → |b' t| ≤ L) (T : ℝ≥0) :
    ‖trace 1 b T‖ ≤ (L : ℝ)*T+2*Real.sqrt T := by
  have hh := smooth_raw_trace_position_bounds b T b'
    (fun t ht => (hd t ht.1).mono Icc_subset_Ici_self) L.coe_nonneg (fun t ht => hb t ht.1)
  have him : (trace 1 b T).im ≤ 2*Real.sqrt T := by
    nlinarith [Real.sq_sqrt T.coe_nonneg,Real.sqrt_nonneg (T : ℝ)]
  calc
    _ ≤ |(trace 1 b T).re|+|(trace 1 b T).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (L : ℝ)*T+2*Real.sqrt T := by rw [abs_of_nonneg hh.2.1]; exact add_le_add hh.1 him

theorem continuous_smooth_raw_trace (b : Driver) (b' : ℝ → ℝ) (L : ℝ≥0)
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt (driverValue b) (b' t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → |b' t| ≤ L) :
    Continuous (fun T : ℝ≥0 => trace 1 b T) := by
  have hLip := lipschitz_driverValue_of_bounded_derivative b b' L hd hb
  apply continuous_iff_continuousAt.mpr
  intro T
  by_cases hT : T=0
  · subst T
    change Tendsto (fun T : ℝ≥0 => trace 1 b T) (𝓝 0) (𝓝 (trace 1 b 0))
    rw [smooth_trace_zero b b' L hd hb]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (smooth_trace_norm_le b b' L hd hb)
    have hc : Continuous (fun T : ℝ≥0 => (L : ℝ)*T+2*Real.sqrt T) := by fun_prop
    simpa only [NNReal.coe_zero,mul_zero,Real.sqrt_zero,add_zero] using hc.tendsto 0
  · have hTp : 0 < (T : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hT)
    obtain ⟨ar,har,harT,hsmall⟩ := exists_smooth_window ((T : ℝ)/2) (half_pos hTp) L
    let a : ℝ≥0 := ⟨ar,har.le⟩
    have ha : 0 < a := har
    have haT : a < T := harT.trans_lt (half_lt_self hTp)
    exact (continuousOn_smooth_trace_Icc b b' hLip hd hb a (T+1) ha hsmall).continuousAt
      (Icc_mem_nhds haT (by simp))

end SLEExactGauge.Target

end

end OAI
