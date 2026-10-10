import OAI.Probability.SLE.Loewner.SmoothRawTrace
import OAI.Probability.SLE.Loewner.ReverseHeightUpper

namespace OAI

/-! Quantitative position bounds for the raw smooth-driver trace.
These estimates include time zero and do not assume a capacity witness. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

lemma smooth_raw_inverse_real_bound (b : Driver) (T : ℝ≥0) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (driverValue b)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L)
    {y : ℝ} (hy : 0 < y) :
    |(inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I)).re| ≤ L*T := by
  obtain ⟨q,hq0,hqy,hqd,heq⟩ := exists_raw_reverse_trajectory b T
    ((b T : ℂ)+(y : ℂ)*I) (by simpa [upperHalfPlane] using hy)
  let u (s : ℝ) := driverValue b ((T : ℝ)-s)
  have hreflect (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) :
      (T : ℝ)-s ∈ Icc 0 (T : ℝ) :=
    ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩
  have hu (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt u
      (-b' ((T : ℝ)-s)) (Icc 0 (T : ℝ)) s := by
    have hi : HasDerivWithinAt (fun t : ℝ => (T : ℝ)-t) (-1) (Icc 0 (T : ℝ)) s := by
      simpa using ((hasDerivAt_id s).const_sub (T : ℝ)).hasDerivWithinAt
    convert! (hd _ (hreflect s hs)).comp s hi hreflect using 1
    simp only [mul_neg,mul_one]
  have hh := (reverse_centered_coordinates hL q u (fun s => -b' ((T : ℝ)-s))
    (fun s hs => (hqd s hs.1).mono Icc_subset_Ici_self) hu
    (fun s hs => by simpa using hb _ (hreflect s hs))
    (fun s hs => hy.trans_le (by simpa using hqy s hs.1))
    (by simp [hq0,u,driverValue])).1 T ⟨T.coe_nonneg,le_rfl⟩
  rw [heq]
  simpa only [u,sub_self,driverValue,Real.toNNReal_zero,map_zero,sub_zero] using hh

theorem smooth_raw_trace_position_bounds (b : Driver) (T : ℝ≥0) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (driverValue b)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L) :
    |(trace 1 b T).re| ≤ L*T ∧ 0 ≤ (trace 1 b T).im ∧
      (trace 1 b T).im^2 ≤ 4*T := by
  have ht := tendsto_inverseFlow_smooth_trace b T b' hd hL hb
  have hid : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    nhdsWithin_le_nhds
  refine ⟨?_,?_,?_⟩
  · apply le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp ht |>.abs)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact smooth_raw_inverse_real_bound b T b' hd hL hb hy
  · apply ge_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp ht)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (inverseFlow_mem_upperHalfPlane 1 (by norm_num) b T
      ((b T : ℂ)+(y : ℂ)*I) (by simpa [upperHalfPlane] using hy)).le
  · apply le_of_tendsto_of_tendsto
      ((Complex.continuous_im.continuousAt.tendsto.comp ht).pow 2)
      (show Tendsto (fun y : ℝ => y^2+4*(T : ℝ)) (𝓝[>] 0) (𝓝 (4*(T : ℝ))) from
        by simpa only [zero_pow (by decide : (2:ℕ) ≠ 0),zero_add] using (hid.pow 2).add_const (4*(T : ℝ)))
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa only [Function.comp_apply,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using
      raw_inverse_height_square_le b T ((b T : ℂ)+(y : ℂ)*I)
        (by simpa [upperHalfPlane] using hy)

end SLEExactGauge.Target

end

end OAI
