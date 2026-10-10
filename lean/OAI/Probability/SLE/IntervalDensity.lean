import Mathlib

namespace OAI

/-! Interval Density for chordal SLE. -/

section

section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge

noncomputable def smoothingWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

lemma smoothingWidth_pos (n : ℕ) : 0 < smoothingWidth n := by
  unfold smoothingWidth
  positivity

lemma smoothingWidth_le (n : ℕ) : smoothingWidth n ≤ 1/2 := by
  unfold smoothingWidth
  apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
  norm_num

lemma smoothingWidth_tendsto : Tendsto smoothingWidth atTop (𝓝 0) := by
  unfold smoothingWidth
  simpa [Function.comp_def] using (tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right _ (2 : ℝ) tendsto_natCast_atTop_atTop))

noncomputable def intervalBump (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    ContDiffBump (a+l/2) where
  rIn := (l/2) * (1-smoothingWidth n)
  rOut := (l/2) * (1-smoothingWidth n/2)
  rIn_pos := mul_pos (by linarith) (by have := smoothingWidth_le n; linarith)
  rIn_lt_rOut := by
    apply mul_lt_mul_of_pos_left _ (by linarith)
    have := smoothingWidth_pos n
    linarith

lemma intervalBump_radii (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    l/4 ≤ (intervalBump a l hl n).rIn ∧ (intervalBump a l hl n).rOut < l/2 := by
  dsimp [intervalBump]
  constructor
  · have h := smoothingWidth_le n
    nlinarith
  · have h := smoothingWidth_pos n
    nlinarith

noncomputable def intervalDensity (a l : ℝ) (hl : 0 < l) (n : ℕ) : ℝ → ℝ :=
  (intervalBump a l hl n).normed volume

lemma intervalDensity_smooth (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    ContDiff ℝ ∞ (intervalDensity a l hl n) :=
  (intervalBump a l hl n).contDiff_normed

lemma intervalDensity_nonneg (a l : ℝ) (hl : 0 < l) (n : ℕ) (x : ℝ) :
    0 ≤ intervalDensity a l hl n x :=
  (intervalBump a l hl n).nonneg_normed x

lemma intervalDensity_compact (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    HasCompactSupport (intervalDensity a l hl n) :=
  (intervalBump a l hl n).hasCompactSupport_normed

lemma intervalDensity_integrable (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    Integrable (intervalDensity a l hl n) :=
  (intervalBump a l hl n).integrable_normed

lemma intervalDensity_integral (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    ∫ x, intervalDensity a l hl n x = 1 :=
  (intervalBump a l hl n).integral_normed

lemma intervalDensity_support (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    tsupport (intervalDensity a l hl n) ⊆ Ioo a (a+l) := by
  rw [intervalDensity, (intervalBump a l hl n).tsupport_normed_eq]
  intro x hx
  rw [Real.closedBall_eq_Icc] at hx
  have ho := (intervalBump_radii a l hl n).2
  constructor <;> linarith [hx.1, hx.2]

lemma intervalDensity_bound (a l : ℝ) (hl : 0 < l) (n : ℕ) (x : ℝ) :
    intervalDensity a l hl n x ≤ 2/l := by
  have hh := (intervalBump a l hl n).normed_le_div_measure_closedBall_rIn volume x
  have hp := (intervalBump a l hl n).rIn_pos
  rw [Measure.real, Real.volume_closedBall, ENNReal.toReal_ofReal (by positivity)] at hh
  apply hh.trans
  apply (div_le_div_iff₀ (by positivity) hl).2
  have ha := (intervalBump_radii a l hl n).1
  linarith

lemma intervalBump_integral_tendsto (a l : ℝ) (hl : 0 < l) :
    Tendsto (fun n => ∫ x, intervalBump a l hl n x) atTop (𝓝 l) := by
  have hlow (n : ℕ) : 2*(intervalBump a l hl n).rIn ≤
      ∫ x, intervalBump a l hl n x := by
    have hh := (intervalBump a l hl n).measure_closedBall_le_integral volume
    simpa [Measure.real, Real.volume_closedBall, ENNReal.toReal_ofReal,
      (intervalBump a l hl n).rIn_pos.le] using hh
  have hupp (n : ℕ) : (∫ x, intervalBump a l hl n x) ≤
      2*(intervalBump a l hl n).rOut := by
    have hh := (intervalBump a l hl n).integral_le_measure_closedBall volume
    simpa [Measure.real, Real.volume_closedBall, ENNReal.toReal_ofReal,
      (intervalBump a l hl n).rOut_pos.le] using hh
  have hlo : Tendsto (fun n => 2*(intervalBump a l hl n).rIn) atTop (𝓝 l) := by
    have hh := (smoothingWidth_tendsto.const_sub 1).const_mul (2*(l/2))
    simp only [sub_zero, mul_one, show 2*(l/2)=l by ring] at hh
    convert hh using 1
    ext n
    dsimp [intervalBump]
    ring
  have hup : Tendsto (fun n => 2*(intervalBump a l hl n).rOut) atTop (𝓝 l) := by
    have hh := ((smoothingWidth_tendsto.div_const 2).const_sub 1).const_mul (2*(l/2))
    simp only [zero_div, sub_zero, mul_one, show 2*(l/2)=l by ring] at hh
    convert hh using 1
    ext n
    dsimp [intervalBump]
    ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup hlow hupp

lemma intervalDensity_support_exact (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    tsupport (intervalDensity a l hl n) =
      Icc (a+l*smoothingWidth n/4) (a+l-l*smoothingWidth n/4) := by
  rw [intervalDensity, (intervalBump a l hl n).tsupport_normed_eq,
    Real.closedBall_eq_Icc]
  congr 1 <;> dsimp [intervalBump] <;> ring

lemma intervalDensity_tendsto (a l : ℝ) (hl : 0 < l) (x : ℝ) :
    Tendsto (fun n => intervalDensity a l hl n x) atTop
      (𝓝 ((Ioo a (a+l)).indicator (fun _ => 1/l) x)) := by
  by_cases hx : x ∈ Ioo a (a+l)
  · have hd : dist x (a+l/2) < l/2 := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    have hrin : Tendsto (fun n => (intervalBump a l hl n).rIn) atTop (𝓝 (l/2)) := by
      have hh := (smoothingWidth_tendsto.const_sub 1).const_mul (l/2)
      simpa [intervalBump] using hh
    have he : ∀ᶠ n in atTop, dist x (a+l/2) ≤ (intervalBump a l hl n).rIn := by
      filter_upwards [hrin.eventually (eventually_gt_nhds hd)] with n hn
      exact hn.le
    have hb : Tendsto (fun n => intervalBump a l hl n x) atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with n hn
      exact ((intervalBump a l hl n).one_of_mem_closedBall hn).symm
    rw [indicator_of_mem hx]
    exact hb.div (intervalBump_integral_tendsto a l hl) (ne_of_gt hl)
  · have hh (n : ℕ) : intervalDensity a l hl n x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (intervalDensity_support a l hl n h))
    simp only [indicator_of_notMem hx]
    exact tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hh n).symm)

 
noncomputable def densityPrimitive (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in a..x, f t

lemma densityPrimitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (a x : ℝ) :
    HasDerivAt (densityPrimitive a f) (f x) x := by
  apply intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a x)
  · exact hf.stronglyMeasurable.stronglyMeasurableAtFilter
  · exact hf.continuousAt

lemma densityPrimitive_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ContDiff ℝ ∞ (densityPrimitive a f) := by
  rw [contDiff_infty_iff_deriv]
  have hd := densityPrimitive_hasDerivAt hf.continuous a
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  have he : deriv (densityPrimitive a f) = f := funext fun x => (hd x).deriv
  rw [he]
  exact hf

lemma densityPrimitive_support {f : ℝ → ℝ} {a c d : ℝ}
    (hac : a < c) (hs : Function.support f ⊆ Icc c d) (hzero : ∫ t, f t = 0) :
    tsupport (densityPrimitive a f) ⊆ Icc c d := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hh
  have hz : densityPrimitive a f x = 0 := by
    rcases not_and_or.mp hh with hc | hd
    · apply intervalIntegral.integral_zero_ae
      filter_upwards [] with t ht
      have ht' : t < c := lt_of_le_of_lt ht.2 (max_lt hac (lt_of_not_ge hc))
      by_contra h
      have := (hs h).1
      linarith
    · have hdx : d < x := lt_of_not_ge hd
      rw [densityPrimitive, intervalIntegral.integral_eq_integral_of_support_subset]
      · exact hzero
      · intro t ht
        have hh := hs ht
        exact ⟨hac.trans_le hh.1, hh.2.trans hdx.le⟩
  exact hx hz

lemma densityPrimitive_compact {f : ℝ → ℝ} {a c d : ℝ}
    (hac : a < c) (hs : Function.support f ⊆ Icc c d) (hzero : ∫ t, f t = 0) :
    HasCompactSupport (densityPrimitive a f) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (densityPrimitive_support hac hs hzero)

lemma densityPrimitive_bound {f : ℝ → ℝ} (hf : Integrable f) (a x : ℝ) :
    |densityPrimitive a f x| ≤ ∫ t, |f t| := by
  calc
    _ ≤ ∫ t in Set.uIoc a x, |f t| := by
      simpa only [densityPrimitive, Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm_uIoc (f := f) (a := a) (b := x) (μ := volume))
    _ ≤ _ := integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun t => abs_nonneg _) hf.abs

noncomputable def intervalTransport (a l : ℝ) (hl : 0 < l) (a' : ℝ) (n : ℕ) : ℝ → ℝ :=
  densityPrimitive a (fun x => intervalDensity a' (l/2) (by linarith) n x -
    intervalDensity a l hl n x)

lemma intervalTransport_contDiff (a l : ℝ) (hl : 0 < l) (a' : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (intervalTransport a l hl a' n) :=
  densityPrimitive_contDiff ((intervalDensity_smooth ..).sub (intervalDensity_smooth ..)) a

lemma intervalTransport_hasDerivAt (a l : ℝ) (hl : 0 < l) (a' : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (intervalTransport a l hl a' n)
      (intervalDensity a' (l/2) (by linarith) n x - intervalDensity a l hl n x) x :=
  densityPrimitive_hasDerivAt
    ((intervalDensity_smooth ..).continuous.sub (intervalDensity_smooth ..).continuous) a x

lemma intervalTransport_support (a l : ℝ) (hl : 0 < l) (a' : ℝ)
    (ha : a ≤ a') (ha' : a'+l/2 ≤ a+l) (n : ℕ) :
    tsupport (intervalTransport a l hl a' n) ⊆
      Icc (a+l*smoothingWidth n/8) (a+l-l*smoothingWidth n/8) := by
  have hp : 0 < l*smoothingWidth n := mul_pos hl (smoothingWidth_pos n)
  apply densityPrimitive_support (by linarith : a < a+l*smoothingWidth n/8)
  · intro x hx
    by_cases hc : intervalDensity a' (l/2) (by linarith) n x ≠ 0
    · have hh : x ∈ tsupport (intervalDensity a' (l/2) (by linarith) n) := subset_closure hc
      rw [intervalDensity_support_exact] at hh
      constructor <;> nlinarith [hh.1,hh.2]
    · simp only [not_not] at hc
      have hc' : intervalDensity a l hl n x ≠ 0 := by
        intro hz
        exact hx (by dsimp; rw [hc,hz]; ring)
      have hh : x ∈ tsupport (intervalDensity a l hl n) := subset_closure hc'
      rw [intervalDensity_support_exact] at hh
      constructor <;> nlinarith [hh.1,hh.2]
  · rw [integral_sub (intervalDensity_integrable ..) (intervalDensity_integrable ..),
      intervalDensity_integral, intervalDensity_integral, sub_self]

lemma intervalTransport_compact (a l : ℝ) (hl : 0 < l) (a' : ℝ)
    (ha : a ≤ a') (ha' : a'+l/2 ≤ a+l) (n : ℕ) :
    HasCompactSupport (intervalTransport a l hl a' n) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (intervalTransport_support a l hl a' ha ha' n)

lemma intervalTransport_support_interior (a l : ℝ) (hl : 0 < l) (a' : ℝ)
    (ha : a ≤ a') (ha' : a'+l/2 ≤ a+l) (n : ℕ) :
    tsupport (intervalTransport a l hl a' n) ⊆ Ioo a (a+l) := by
  intro x hx
  have hh := intervalTransport_support a l hl a' ha ha' n hx
  have hp : 0 < l*smoothingWidth n := mul_pos hl (smoothingWidth_pos n)
  constructor <;> linarith [hh.1,hh.2]

lemma intervalTransport_bound (a l : ℝ) (hl : 0 < l) (a' : ℝ) (n : ℕ) (x : ℝ) :
    |intervalTransport a l hl a' n x| ≤ 2 := by
  have hc := intervalDensity_integrable a' (l/2) (by linarith) n
  have hp := intervalDensity_integrable a l hl n
  apply (densityPrimitive_bound (hc.sub hp) a x).trans
  calc
    _ ≤ ∫ t, intervalDensity a' (l/2) (by linarith) n t + intervalDensity a l hl n t := by
      apply integral_mono (hc.sub hp).abs (hc.add hp)
      intro t
      change |intervalDensity a' (l/2) _ n t - intervalDensity a l hl n t| ≤
        intervalDensity a' (l/2) _ n t + intervalDensity a l hl n t
      apply abs_le.mpr
      have hc := intervalDensity_nonneg a' (l/2) (by linarith) n t
      have hp := intervalDensity_nonneg a l hl n t
      constructor <;> linarith
    _ = 2 := by
      rw [integral_add hc hp, intervalDensity_integral, intervalDensity_integral]
      norm_num

lemma intervalTransport_integrable (a l : ℝ) (hl : 0 < l) (a' : ℝ)
    (ha : a ≤ a') (ha' : a'+l/2 ≤ a+l) (n : ℕ) :
    Integrable (intervalTransport a l hl a' n) :=
  (intervalTransport_contDiff ..).continuous.integrable_of_hasCompactSupport (μ := volume)
    (intervalTransport_compact a l hl a' ha ha' n)

lemma intervalTransport_integral_abs_le (a l : ℝ) (hl : 0 < l) (a' : ℝ)
    (ha : a ≤ a') (ha' : a'+l/2 ≤ a+l) (n : ℕ) :
    ∫ x, |intervalTransport a l hl a' n x| ≤ 2*l := by
  have hs : ∀ x, x ∉ Icc a (a+l) → |intervalTransport a l hl a' n x| = 0 := by
    intro x hx
    have he : intervalTransport a l hl a' n x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hh
      have hh' := intervalTransport_support_interior a l hl a' ha ha' n hh
      exact hx ⟨hh'.1.le,hh'.2.le⟩
    rw [he, abs_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs]
  calc
    _ ≤ ∫ x in Icc a (a+l), (2:ℝ) := by
      apply integral_mono_ae
        ((intervalTransport_integrable a l hl a' ha ha' n).abs.restrict)
        (integrable_const 2)
      exact Eventually.of_forall fun x => intervalTransport_bound a l hl a' n x
    _ = 2*l := by
      simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
        Real.volume_Icc, add_sub_cancel_left, ENNReal.toReal_ofReal hl.le, smul_eq_mul]
      ring

def complexTensor (f g : ℝ → ℝ) (z : ℂ) : ℝ := f z.re * g z.im

lemma complexTensor_contDiff {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (complexTensor f g) :=
  (hf.comp Complex.reCLM.contDiff).mul (hg.comp Complex.imCLM.contDiff)

lemma complexTensor_support (f g : ℝ → ℝ) :
    tsupport (complexTensor f g) ⊆
      Complex.equivRealProdCLM ⁻¹' (tsupport f ×ˢ tsupport g) := by
  apply closure_minimal _
    (((isClosed_tsupport f).prod (isClosed_tsupport g)).preimage
      Complex.equivRealProdCLM.continuous)
  intro z hz
  have hh : f z.re * g z.im ≠ 0 := hz
  exact ⟨subset_closure (mul_ne_zero_iff.mp hh).1,
    subset_closure (mul_ne_zero_iff.mp hh).2⟩

lemma complexTensor_compact {f g : ℝ → ℝ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (complexTensor f g) :=
  (Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr
    (hf.prod hg)).of_isClosed_subset (isClosed_tsupport _) (complexTensor_support f g)

lemma complexTensor_integral (f g : ℝ → ℝ) :
    (∫ z, complexTensor f g z) = (∫ x, f x) * (∫ y, g y) := by
  have he := Complex.volume_preserving_equiv_real_prod.integral_comp
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => f p.1 * g p.2)
  simp only [Complex.measurableEquivRealProd_apply] at he
  unfold complexTensor
  rw [he, Measure.volume_eq_prod]
  exact integral_prod_mul f g

lemma complexTensor_integral_abs (f g : ℝ → ℝ) :
    (∫ z, |complexTensor f g z|) = (∫ x, |f x|) * (∫ y, |g y|) := by
  simpa only [complexTensor, abs_mul] using
    complexTensor_integral (fun x => |f x|) (fun y => |g y|)

lemma complexTensor_deriv_re {f g : ℝ → ℝ} {f' g' : ℝ} {z : ℂ}
    (hf : HasDerivAt f f' z.re) (hg : HasDerivAt g g' z.im) :
    (fderiv ℝ (complexTensor f g) z) (1 : ℂ) = f' * g z.im := by
  have hh := (hf.hasFDerivAt.comp z Complex.reCLM.hasFDerivAt).mul
    (hg.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt)
  change fderiv ℝ ((f ∘ Complex.re) * (g ∘ Complex.im)) z 1 = _
  rw [hh.fderiv]
  simp [mul_comm]

lemma complexTensor_deriv_im {f g : ℝ → ℝ} {f' g' : ℝ} {z : ℂ}
    (hf : HasDerivAt f f' z.re) (hg : HasDerivAt g g' z.im) :
    (fderiv ℝ (complexTensor f g) z) Complex.I = f z.re * g' := by
  have hh := (hf.hasFDerivAt.comp z Complex.reCLM.hasFDerivAt).mul
    (hg.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt)
  change fderiv ℝ ((f ∘ Complex.re) * (g ∘ Complex.im)) z Complex.I = _
  rw [hh.fderiv]
  simp

noncomputable def rectangleDensity (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (n : ℕ) : ℂ → ℝ :=
  complexTensor (intervalDensity a lx hx n) (intervalDensity b ly hy n)

noncomputable def rectangleTransportX (a _b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (n : ℕ) : ℂ → ℝ :=
  complexTensor (intervalTransport a lx hx a' n)
    (intervalDensity b' (ly/2) (by linarith) n)

noncomputable def rectangleTransportY (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (_a' b' : ℝ) (n : ℕ) : ℂ → ℝ :=
  complexTensor (intervalDensity a lx hx n)
    (intervalTransport b ly hy b' n)

lemma rectangleTransportX_contDiff (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (rectangleTransportX a b lx ly hx hy a' b' n) :=
  complexTensor_contDiff (intervalTransport_contDiff ..) (intervalDensity_smooth ..)

lemma rectangleTransportY_contDiff (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (rectangleTransportY a b lx ly hx hy a' b' n) :=
  complexTensor_contDiff (intervalDensity_smooth ..) (intervalTransport_contDiff ..)

lemma rectangleTransportX_compact (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (ha : a ≤ a') (ha' : a'+lx/2 ≤ a+lx) (n : ℕ) :
    HasCompactSupport (rectangleTransportX a b lx ly hx hy a' b' n) :=
  complexTensor_compact (intervalTransport_compact a lx hx a' ha ha' n)
    (intervalDensity_compact ..)

lemma rectangleTransportY_compact (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (hb : b ≤ b') (hb' : b'+ly/2 ≤ b+ly) (n : ℕ) :
    HasCompactSupport (rectangleTransportY a b lx ly hx hy a' b' n) :=
  complexTensor_compact (intervalDensity_compact ..)
    (intervalTransport_compact b ly hy b' hb hb' n)

lemma rectangleTransportX_support (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (ha : a ≤ a') (ha' : a'+lx/2 ≤ a+lx)
    (hb : b ≤ b') (hb' : b'+ly/2 ≤ b+ly) (n : ℕ) :
    tsupport (rectangleTransportX a b lx ly hx hy a' b' n) ⊆
      {z | a < z.re ∧ z.re < a+lx ∧ b < z.im ∧ z.im < b+ly} := by
  intro z hz
  have hh := complexTensor_support _ _ hz
  have hr := intervalTransport_support_interior a lx hx a' ha ha' n hh.1
  have hi := intervalDensity_support b' (ly/2) (by linarith) n hh.2
  exact ⟨hr.1, hr.2, hb.trans_lt hi.1, hi.2.trans_le hb'⟩

lemma rectangleTransportY_support (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (hb : b ≤ b') (hb' : b'+ly/2 ≤ b+ly) (n : ℕ) :
    tsupport (rectangleTransportY a b lx ly hx hy a' b' n) ⊆
      {z | a < z.re ∧ z.re < a+lx ∧ b < z.im ∧ z.im < b+ly} := by
  intro z hz
  have hh := complexTensor_support _ _ hz
  have hr := intervalDensity_support a lx hx n hh.1
  have hi := intervalTransport_support_interior b ly hy b' hb hb' n hh.2
  exact ⟨hr.1, hr.2, hi.1, hi.2⟩

lemma rectangleTransport_divergence (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (n : ℕ) (z : ℂ) :
    (fderiv ℝ (rectangleTransportX a b lx ly hx hy a' b' n) z) 1 +
      (fderiv ℝ (rectangleTransportY a b lx ly hx hy a' b' n) z) Complex.I =
      rectangleDensity a' b' (lx/2) (ly/2) (by linarith) (by linarith) n z -
        rectangleDensity a b lx ly hx hy n z := by
  unfold rectangleTransportX rectangleTransportY
  rw [complexTensor_deriv_re (intervalTransport_hasDerivAt ..)
    (((intervalDensity_smooth ..).differentiable (by simp)) _).hasDerivAt]
  rw [complexTensor_deriv_im
    (((intervalDensity_smooth ..).differentiable (by simp)) _).hasDerivAt
    (intervalTransport_hasDerivAt ..)]
  dsimp [rectangleDensity, complexTensor]
  ring

lemma rectangleTransportX_bound (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (n : ℕ) (z : ℂ) :
    |rectangleTransportX a b lx ly hx hy a' b' n z| ≤ 8/ly := by
  unfold rectangleTransportX complexTensor
  rw [abs_mul, abs_of_nonneg (intervalDensity_nonneg ..)]
  calc
    _ ≤ 2 * (2/(ly/2)) := mul_le_mul (intervalTransport_bound ..)
      (intervalDensity_bound ..) (intervalDensity_nonneg ..) (by norm_num)
    _ = _ := by field_simp; ring

lemma rectangleTransportY_bound (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (n : ℕ) (z : ℂ) :
    |rectangleTransportY a b lx ly hx hy a' b' n z| ≤ 4/lx := by
  unfold rectangleTransportY complexTensor
  rw [abs_mul, abs_of_nonneg (intervalDensity_nonneg ..)]
  calc
    _ ≤ (2/lx) * 2 := mul_le_mul (intervalDensity_bound ..)
      (intervalTransport_bound ..) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma intervalDensity_integral_abs (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    (∫ x, |intervalDensity a l hl n x|) = 1 := by
  simp_rw [abs_of_nonneg (intervalDensity_nonneg a l hl n _)]
  exact intervalDensity_integral ..

lemma rectangleTransportX_integral_abs (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (ha : a ≤ a') (ha' : a'+lx/2 ≤ a+lx) (n : ℕ) :
    ∫ z, |rectangleTransportX a b lx ly hx hy a' b' n z| ≤ 2*lx := by
  rw [rectangleTransportX, complexTensor_integral_abs, intervalDensity_integral_abs, mul_one]
  exact intervalTransport_integral_abs_le a lx hx a' ha ha' n

lemma rectangleTransportY_integral_abs (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (hb : b ≤ b') (hb' : b'+ly/2 ≤ b+ly) (n : ℕ) :
    ∫ z, |rectangleTransportY a b lx ly hx hy a' b' n z| ≤ 2*ly := by
  rw [rectangleTransportY, complexTensor_integral_abs, intervalDensity_integral_abs, one_mul]
  exact intervalTransport_integral_abs_le b ly hy b' hb hb' n

noncomputable def scaleLength (j : ℕ) : ℝ := 1/(2:ℝ)^j
noncomputable def scaleOrigin (t : ℝ) (j : ℕ) : ℝ := t * (1-scaleLength j)

lemma scaleLength_pos (j : ℕ) : 0 < scaleLength j := by
  unfold scaleLength; positivity
lemma scaleLength_le_one (j : ℕ) : scaleLength j ≤ 1 := by
  unfold scaleLength
  exact (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
lemma scaleLength_zero : scaleLength 0 = 1 := by simp [scaleLength]
lemma scaleLength_succ (j : ℕ) : scaleLength (j+1) = scaleLength j/2 := by
  simp [scaleLength, pow_succ, div_mul_eq_div_div]
lemma scaleOrigin_zero (t : ℝ) : scaleOrigin t 0 = 0 := by simp [scaleOrigin, scaleLength]
lemma scaleOrigin_nonneg {t : ℝ} (ht : 0 ≤ t) (j : ℕ) : 0 ≤ scaleOrigin t j :=
  mul_nonneg ht (sub_nonneg.mpr (scaleLength_le_one j))
lemma scaleOrigin_add_le_one {t : ℝ} (ht : t ≤ 1) (j : ℕ) :
    scaleOrigin t j + scaleLength j ≤ 1 := by
  have hh := mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr (scaleLength_le_one j))
  dsimp [scaleOrigin]
  linarith
lemma scaleOrigin_step {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    scaleOrigin t j ≤ scaleOrigin t (j+1) := by
  simp only [scaleOrigin, scaleLength_succ]
  have := mul_nonneg ht (scaleLength_pos j).le
  nlinarith
lemma scaleOrigin_right_step {t : ℝ} (ht : t ≤ 1) (j : ℕ) :
    scaleOrigin t (j+1) + scaleLength j/2 ≤ scaleOrigin t j + scaleLength j := by
  simp only [scaleOrigin, scaleLength_succ]
  have := mul_le_mul_of_nonneg_right ht (scaleLength_pos j).le
  nlinarith

lemma dyadic_position_param (k : ℕ) (hk : k ≠ 0) (i : Fin (2^k)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ scaleOrigin t k = (i:ℝ)/(2:ℝ)^k := by
  have hp : (1:ℝ) < 2^k := one_lt_pow₀ (by norm_num) hk
  have hi : (i:ℝ) + 1 ≤ (2:ℝ)^k := by
    exact_mod_cast i.isLt
  refine ⟨(i:ℝ)/((2:ℝ)^k-1), by positivity, ?_, ?_⟩
  · apply (div_le_one (by linarith)).2
    linarith
  · unfold scaleOrigin scaleLength
    have hp0 : (2:ℝ)^k ≠ 0 := by positivity
    have hp1 : (2:ℝ)^k-1 ≠ 0 := by linarith
    field_simp

lemma dyadic_sum (n : ℕ) : ∑ j ∈ Finset.range n, (2 : ℝ)^j = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

 

lemma dyadic_sum_square (a : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A) (n : ℕ)
    (ha : ∀ j < n, 0 ≤ a j ∧ a j ≤ A * 2^j) :
    (∑ j ∈ Finset.range n, a j)^2 ≤
      3 * A * ∑ j ∈ Finset.range n, (2 : ℝ)^j * a j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ha n (Nat.lt_succ_self n)
    have ha' : ∀ j < n, 0 ≤ a j ∧ a j ≤ A * 2^j :=
      fun j hj => ha j (Nat.lt_trans hj (Nat.lt_succ_self n))
    have hs0 : 0 ≤ ∑ j ∈ Finset.range n, a j :=
      Finset.sum_nonneg fun j hj => (ha' j (Finset.mem_range.mp hj)).1
    have hs : (∑ j ∈ Finset.range n, a j) ≤ A * (2^n - 1) := by
      calc
        _ ≤ ∑ j ∈ Finset.range n, A * 2^j :=
          Finset.sum_le_sum fun j hj => (ha' j (Finset.mem_range.mp hj)).2
        _ = _ := by rw [← Finset.mul_sum, dyadic_sum]
    have hcross := mul_le_mul_of_nonneg_right hs hn.1
    have hsquare := mul_le_mul_of_nonneg_right hn.2 hn.1
    have hnonneg : 0 ≤ A * a n := mul_nonneg hA hn.1
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hi := ih ha'
    nlinarith

 

theorem integral_sum_kernel_sq_le
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} (K : ℕ → X → E) (A B : ℝ) (n : ℕ)
    (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hK : ∀ j < n, Integrable (K j) μ)
    (hbound : ∀ j < n, ∀ x, ‖K j x‖ ≤ A * 2^j)
    (h₁ : ∀ j < n, ∫ x, ‖K j x‖ ∂μ ≤ B / 2^j) :
    (∫ x, ‖∑ j ∈ Finset.range n, K j x‖^2 ∂μ) ≤ 3 * A * B * n := by
  have hb (x : X) : ‖∑ j ∈ Finset.range n, K j x‖^2 ≤
      3 * A * ∑ j ∈ Finset.range n, (2 : ℝ)^j * ‖K j x‖ := by
    have hz : 0 ≤ ∑ j ∈ Finset.range n, ‖K j x‖ := by positivity
    have hn := norm_sum_le (Finset.range n) (fun j => K j x)
    exact (sq_le_sq₀ (norm_nonneg _) hz).mpr hn |>.trans
      (dyadic_sum_square (fun j => ‖K j x‖) A hA n
        (fun j hj => ⟨norm_nonneg _, hbound j hj x⟩))
  have hi : Integrable
      (fun x => 3 * A * ∑ j ∈ Finset.range n, (2 : ℝ)^j * ‖K j x‖) μ := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ fun j hj =>
      ((hK j (Finset.mem_range.mp hj)).norm).const_mul _
  have hs : AEStronglyMeasurable (fun x => ∑ j ∈ Finset.range n, K j x) μ := by
    convert Finset.aestronglyMeasurable_sum (Finset.range n) (fun j hj =>
        (hK j (Finset.mem_range.mp hj)).aestronglyMeasurable) using 1
    funext x
    exact (Finset.sum_apply x _ _).symm
  have hi' : Integrable (fun x => ‖∑ j ∈ Finset.range n, K j x‖^2) μ := by
    apply hi.mono' (hs.norm.pow 2)
    exact Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x
  calc
    _ ≤ ∫ x, 3 * A * ∑ j ∈ Finset.range n, (2 : ℝ)^j * ‖K j x‖ ∂μ :=
      integral_mono hi' hi hb
    _ = 3 * A * ∑ j ∈ Finset.range n, (2 : ℝ)^j * ∫ x, ‖K j x‖ ∂μ := by
      rw [integral_const_mul, integral_finsetSum]
      · simp_rw [integral_const_mul]
      · intro j hj
        exact ((hK j (Finset.mem_range.mp hj)).norm).const_mul _
    _ ≤ 3 * A * ∑ j ∈ Finset.range n, B := by
      gcongr with j hj
      have hp : 0 < (2 : ℝ)^j := by positivity
      have hh := mul_le_mul_of_nonneg_left (h₁ j (Finset.mem_range.mp hj)) hp.le
      simpa [mul_div_cancel₀ B (ne_of_gt hp)] using hh
    _ = _ := by simp; ring

def openUnitStrip : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < Real.pi}

 

def SourceIsStripWeakGradient (u : ℂ → ℝ) (D : ℂ → ℂ) : Prop :=
  MemLp u 2 (volume.restrict openUnitStrip) ∧
  MemLp D 2 (volume.restrict openUnitStrip) ∧
  ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ openUnitStrip →
    (∫ z in openUnitStrip, u z * (fderiv ℝ φ z) (1:ℂ)) =
      -(∫ z in openUnitStrip, (D z).re * φ z) ∧
    (∫ z in openUnitStrip, u z * (fderiv ℝ φ z) Complex.I) =
      -(∫ z in openUnitStrip, (D z).im * φ z)

noncomputable def stripDirichletEnergy (D : ℂ → ℂ) : ℝ :=
  ∫ z in openUnitStrip, ‖D z‖^2

lemma openUnitStrip_isOpen : IsOpen openUnitStrip := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))

lemma openUnitStrip_measure_lt_top : volume openUnitStrip < ⊤ := by
  have hs : openUnitStrip ⊆ Metric.closedBall (0:ℂ) (1+Real.pi) := by
    intro z hz
    change 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < Real.pi at hz
    rw [Metric.mem_closedBall,dist_zero_right]
    have hn := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz.1,abs_of_pos hz.2.2.1] at hn
    linarith [hz.2.1,hz.2.2.2]
  exact (measure_mono hs).trans_lt (isCompact_closedBall (0:ℂ) (1+Real.pi)).measure_lt_top

instance finite_openUnitStrip : IsFiniteMeasure (volume.restrict openUnitStrip) :=
  isFiniteMeasure_restrict.mpr openUnitStrip_measure_lt_top.ne

end SLEExactGauge
end
end

end OAI
