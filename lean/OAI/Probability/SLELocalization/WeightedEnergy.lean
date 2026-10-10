import Mathlib

namespace OAI


/-! Conformal localization and Rectangle Energy estimates. -/

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

lemma integral_mul_square_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, f x^2 ∂μ)*(∫ x, g x^2 ∂μ) := by
  have hi {a b : α → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
      inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x*b x ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp,hb.coeFn_toLp] with x hx hy
    rw [hx,hy]
    change b x*a x = a x*b x
    ring
  have hn := norm_inner_le_norm (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [mul_pow,← real_inner_self_eq_norm_sq (hf.toLp f),← real_inner_self_eq_norm_sq (hg.toLp g),
    hi hf hg,hi hf hf,hi hg hg] at hh
  simpa only [Real.norm_eq_abs,sq_abs,← sq] using hh

lemma continuousOn_memLp_two_Ioc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) : MemLp f 2 (volume.restrict (Ioc a b)) := by
  apply (memLp_two_iff_integrable_sq ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)).2
  exact ((hf.pow 2).intervalIntegrable_of_Icc hab).1

lemma weighted_interval_energy {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {F D : ℝ → ℝ} (hD : ContinuousOn D (Icc a b))
    (hF : ∀ s ∈ Icc a b, HasDerivAt F (D s) s) :
    (F b-F a)^2 ≤ Real.log (b/a)*(∫ s in a..b, s*(D s)^2) := by
  let f := fun s : ℝ => Real.sqrt s*D s
  let g := fun s : ℝ => (Real.sqrt s)⁻¹
  have hs (s : ℝ) (hs : s ∈ Icc a b) : 0 < s := ha.trans_le hs.1
  have hf : ContinuousOn f (Icc a b) := Real.continuous_sqrt.continuousOn.mul hD
  have hg : ContinuousOn g (Icc a b) := Real.continuous_sqrt.continuousOn.inv₀
    (fun s hs' => (Real.sqrt_pos.2 (hs s hs')).ne')
  have hc := integral_mul_square_le (continuousOn_memLp_two_Ioc hab hf)
    (continuousOn_memLp_two_Ioc hab hg)
  have hfg : (∫ s in Ioc a b, f s*g s) = F b-F a := by
    calc
      _ = ∫ s in a..b, D s := by
        rw [intervalIntegral.integral_of_le hab]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro s hs'
        dsimp [f,g]
        have hne := (Real.sqrt_pos.2 (hs s (Ioc_subset_Icc_self hs'))).ne'
        field_simp
      _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs' => hF s (by simpa only [uIcc_of_le hab] using hs'))
        (hD.intervalIntegrable_of_Icc hab)
  have hff : (∫ s in Ioc a b, f s^2) = ∫ s in a..b, s*(D s)^2 := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs'
    dsimp only [f]
    rw [mul_pow,Real.sq_sqrt (hs s (Ioc_subset_Icc_self hs')).le]
  have hgg : (∫ s in Ioc a b, g s^2) = Real.log (b/a) := by
    calc
      _ = ∫ s in a..b, s⁻¹ := by
        rw [intervalIntegral.integral_of_le hab]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro s hs'
        dsimp only [g]
        rw [inv_pow,Real.sq_sqrt (hs s (Ioc_subset_Icc_self hs')).le]
      _ = _ := by
        apply integral_inv
        rw [uIcc_of_le hab]
        intro hz
        exact (not_le_of_gt ha) hz.1
  rw [hfg,hff,hgg] at hc
  simpa only [mul_comm] using hc

def radialTruncation (H : ℝ) (q : ℂ) (r : ℝ) (w : ℂ) : ℝ :=
  min H (Real.log (max r ‖w-q‖/r))

lemma radialTruncation_source {r : ℝ} (hr : 0 < r) (H : ℝ) (q w : ℂ) :
    radialTruncation H q r w = min H (max 0 (Real.log (‖w-q‖/r))) := by
  unfold radialTruncation
  by_cases h : ‖w-q‖ ≤ r
  · rw [max_eq_left h,div_self hr.ne',Real.log_one,
      max_eq_left (Real.log_nonpos (div_nonneg (norm_nonneg _) hr.le) ((div_le_one hr).2 h))]
  · have hh : r < ‖w-q‖ := lt_of_not_ge h
    rw [max_eq_right hh.le,max_eq_right (Real.log_nonneg ((one_le_div hr).2 hh.le))]

lemma radialTruncation_bounds {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q w : ℂ) :
    0 ≤ radialTruncation H q r w ∧ radialTruncation H q r w ≤ H := by
  unfold radialTruncation
  exact ⟨le_min hH (Real.log_nonneg ((one_le_div hr).2 (le_max_left _ _))),min_le_left _ _⟩

lemma radialTruncation_continuous {r : ℝ} (hr : 0 < r) (H : ℝ) (q : ℂ) :
    Continuous (radialTruncation H q r) := by
  have hm : Continuous (fun w : ℂ => max r ‖w-q‖/r) :=
    (continuous_const.max ((continuous_id.sub continuous_const).norm)).div_const r
  exact continuous_const.min (hm.log (fun w => (div_pos (lt_of_lt_of_le hr (le_max_left _ _)) hr).ne'))

lemma radialTruncation_zero {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) {q w : ℂ}
    (hw : ‖w-q‖ ≤ r) : radialTruncation H q r w = 0 := by
  simp only [radialTruncation,max_eq_left hw,div_self hr.ne',Real.log_one,min_eq_right hH]

lemma radialTruncation_top {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) {q w : ℂ}
    (hw : Real.exp H*r ≤ ‖w-q‖) : radialTruncation H q r w = H := by
  have he : 1 ≤ Real.exp H := Real.one_le_exp_iff.2 hH
  have hrw : r ≤ ‖w-q‖ := (le_mul_of_one_le_left hr.le he).trans hw
  have hn : 0 < ‖w-q‖/r := div_pos (hr.trans_le hrw) hr
  have hl : H ≤ Real.log (‖w-q‖/r) :=
    (Real.le_log_iff_exp_le hn).2 ((le_div_iff₀ hr).2 hw)
  simp only [radialTruncation,max_eq_right hrw,min_eq_left hl]

lemma radialTruncation_middle {H r : ℝ} (hr : 0 < r) {q w : ℂ}
    (hw : r < ‖w-q‖) (hw' : ‖w-q‖ < Real.exp H*r) :
    radialTruncation H q r w = (1/2:ℝ)*Real.log (‖w-q‖^2)-Real.log r := by
  have hn := hr.trans hw
  have hl : Real.log (‖w-q‖/r) < H :=
    (Real.log_lt_iff_lt_exp (div_pos hn hr)).2 ((div_lt_iff₀ hr).2 hw')
  rw [radialTruncation,max_eq_right hw.le,min_eq_right hl.le,
    Real.log_div hn.ne' hr.ne',Real.log_pow]
  ring

lemma log_normSq_fderiv_le {F : ℂ → ℂ} {z q : ℂ} (hd : DifferentiableAt ℂ F z)
    (hn : 0 < ‖F z-q‖) (r : ℝ) :
    ‖fderiv ℝ (fun w => (1/2:ℝ)*Real.log (‖F w-q‖^2)-Real.log r) z‖ ≤
      ‖deriv F z‖/‖F z-q‖ := by
  let A := (ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ
  have hA : ‖A‖ = ‖deriv F z‖ := by
    dsimp [A]
    rw [ContinuousLinearMap.norm_restrictScalars,ContinuousLinearMap.norm_toSpanSingleton]
  have hF : HasFDerivAt F A z := hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hs := ((hF.sub_const q).norm_sq.log (pow_ne_zero 2 hn.ne')).const_mul (1/2:ℝ)
  have hs' := hs.sub_const (Real.log r)
  have hd' : HasFDerivAt
      (fun w => (1/2:ℝ)*Real.log (‖F w-q‖^2)-Real.log r)
      ((‖F z-q‖^2)⁻¹ • (innerSL ℝ (F z-q)).comp A) z := by
    convert! hs' using 1
    ext v
    simp
    ring
  rw [hd'.fderiv,norm_smul,Real.norm_eq_abs,abs_inv,abs_pow,abs_norm]
  have hb := (innerSL ℝ (F z-q)).opNorm_comp_le A
  rw [innerSL_apply_norm,hA] at hb
  calc
    (‖F z-q‖^2)⁻¹*‖(innerSL ℝ (F z-q)).comp A‖ ≤
        (‖F z-q‖^2)⁻¹*(‖F z-q‖*‖deriv F z‖) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ‖deriv F z‖/‖F z-q‖ := by field_simp

lemma radialTruncation_fderiv_bound {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r)
    {F : ℂ → ℂ} {z q : ℂ} (hd : DifferentiableAt ℂ F z) :
    ‖fderiv ℝ (radialTruncation H q r ∘ F) z‖^2 ≤
      if r < ‖F z-q‖ ∧ ‖F z-q‖ < Real.exp H*r then
        ‖deriv F z‖^2/‖F z-q‖^2 else 0 := by
  by_cases hlow : ‖F z-q‖ ≤ r
  · have hz : fderiv ℝ (radialTruncation H q r ∘ F) z = 0 := by
      apply IsLocalMin.fderiv_eq_zero
      filter_upwards with w
      change radialTruncation H q r (F z) ≤ radialTruncation H q r (F w)
      rw [radialTruncation_zero hH hr hlow]
      exact (radialTruncation_bounds hH hr q _).1
    rw [hz]
    simp [not_lt_of_ge hlow]
  · have hl : r < ‖F z-q‖ := lt_of_not_ge hlow
    by_cases hhigh : Real.exp H*r ≤ ‖F z-q‖
    · have hz : fderiv ℝ (radialTruncation H q r ∘ F) z = 0 := by
        apply IsLocalMax.fderiv_eq_zero
        filter_upwards with w
        change radialTruncation H q r (F w) ≤ radialTruncation H q r (F z)
        rw [radialTruncation_top hH hr hhigh]
        exact (radialTruncation_bounds hH hr q _).2
      rw [hz]
      simp [not_lt_of_ge hhigh]
    · have hh : ‖F z-q‖ < Real.exp H*r := lt_of_not_ge hhigh
      have hc : ContinuousAt (fun w => ‖F w-q‖) z := (hd.continuousAt.sub continuousAt_const).norm
      have he : (radialTruncation H q r ∘ F) =ᶠ[𝓝 z]
          (fun w => (1/2:ℝ)*Real.log (‖F w-q‖^2)-Real.log r) := by
        filter_upwards [continuousAt_const.eventually_lt hc hl,
          hc.eventually_lt continuousAt_const hh] with w hw hw'
        exact radialTruncation_middle hr hw hw'
      rw [he.fderiv_eq,ite_eq_left ⟨hl,hh⟩]
      have ht := pow_le_pow_left₀ (norm_nonneg _) (log_normSq_fderiv_le hd (hr.trans hl) r) 2
      simpa only [div_pow] using ht

lemma radialTruncation_lipschitz {r : ℝ} (hr : 0 < r) (H : ℝ) (q : ℂ) :
    LipschitzWith ⟨1/r,by positivity⟩ (radialTruncation H q r) := by
  let K : ℝ≥0 := ⟨1/r,by positivity⟩
  have hlog : LipschitzOnWith K Real.log (Ici r) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx => Real.differentiableAt_log (hr.trans_le hx).ne') _ (convex_Ici r)
    intro x hx
    change ‖deriv Real.log x‖ ≤ 1/r
    rw [Real.deriv_log,Real.norm_of_nonneg (inv_nonneg.2 (hr.trans_le hx).le),one_div]
    exact inv_anti₀ hr hx
  have hnorm : LipschitzWith 1 (fun w : ℂ => ‖w-q‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist ‖x-q‖ ‖y-q‖ ≤ ‖(x-q)-(y-q)‖ := dist_norm_norm_le _ _
      _ = ‖x-y‖ := by congr 1; abel
      _ = (1:ℝ≥0)*dist x y := by simp [dist_eq_norm]
  have hmax := hnorm.const_max r
  have hl : LipschitzWith K (fun w : ℂ => Real.log (max r ‖w-q‖)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hlog.dist_le_mul (max r ‖x-q‖) (show r ≤ max r ‖x-q‖ from le_max_left _ _) (max r ‖y-q‖) (show r ≤ max r ‖y-q‖ from le_max_left _ _)).trans
      (mul_le_mul_of_nonneg_left (by simpa using hmax.dist_le_mul x y) K.coe_nonneg)
  have hsub : LipschitzWith K (fun w : ℂ => Real.log (max r ‖w-q‖)-Real.log r) := by
    simpa using hl.sub (LipschitzWith.const (Real.log r))
  have he : radialTruncation H q r = fun w : ℂ => min H (Real.log (max r ‖w-q‖)-Real.log r) := by
    ext w
    rw [radialTruncation,Real.log_div (hr.trans_le (le_max_left _ _)).ne' hr.ne']
  rw [he]
  exact hsub.const_min H

lemma radialTruncation_along_C1_AC {r : ℝ} (hr : 0 < r) (H : ℝ) (q : ℂ)
    {G : ℝ → ℂ} {a b : ℝ} (hG : ContDiffOn ℝ 1 G (uIcc a b)) :
    AbsolutelyContinuousOnInterval (radialTruncation H q r ∘ G) a b := by
  obtain ⟨K,hK⟩ := hG.exists_lipschitzOnWith (by norm_num) (convex_uIcc _ _) isCompact_uIcc
  exact ((radialTruncation_lipschitz hr H q).comp_lipschitzOnWith hK).absolutelyContinuousOnInterval

lemma radialTruncation_along_C1_FTC {r : ℝ} (hr : 0 < r) (H : ℝ) (q : ℂ)
    {G : ℝ → ℂ} {a b : ℝ} (hG : ContDiffOn ℝ 1 G (uIcc a b)) :
    (∫ s in a..b, deriv (radialTruncation H q r ∘ G) s) =
      radialTruncation H q r (G b)-radialTruncation H q r (G a) :=
  (radialTruncation_along_C1_AC hr H q hG).integral_deriv_eq_sub

lemma radialTruncation_directional_deriv {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r)
    (q : ℂ) {F : ℂ → ℂ} {c : ℝ → ℂ} {d : ℂ} {t : ℝ}
    (hF : DifferentiableAt ℂ F (c t)) (hc : HasDerivAt c d t) :
    deriv (radialTruncation H q r ∘ F ∘ c) t =
      fderiv ℝ (radialTruncation H q r ∘ F) (c t) d := by
  by_cases hl : ‖F (c t)-q‖ ≤ r
  · have hz : fderiv ℝ (radialTruncation H q r ∘ F) (c t) = 0 := by
      apply IsLocalMin.fderiv_eq_zero
      filter_upwards with w
      change radialTruncation H q r (F (c t)) ≤ radialTruncation H q r (F w)
      rw [radialTruncation_zero hH hr hl]
      exact (radialTruncation_bounds hH hr q _).1
    rw [hz,zero_apply]
    apply IsLocalMin.deriv_eq_zero
    filter_upwards with s
    change radialTruncation H q r (F (c t)) ≤ radialTruncation H q r (F (c s))
    rw [radialTruncation_zero hH hr hl]
    exact (radialTruncation_bounds hH hr q _).1
  · have hl' := lt_of_not_ge hl
    by_cases hh : Real.exp H*r ≤ ‖F (c t)-q‖
    · have hz : fderiv ℝ (radialTruncation H q r ∘ F) (c t) = 0 := by
        apply IsLocalMax.fderiv_eq_zero
        filter_upwards with w
        change radialTruncation H q r (F w) ≤ radialTruncation H q r (F (c t))
        rw [radialTruncation_top hH hr hh]
        exact (radialTruncation_bounds hH hr q _).2
      rw [hz,zero_apply]
      apply IsLocalMax.deriv_eq_zero
      filter_upwards with s
      change radialTruncation H q r (F (c s)) ≤ radialTruncation H q r (F (c t))
      rw [radialTruncation_top hH hr hh]
      exact (radialTruncation_bounds hH hr q _).2
    · have hh' := lt_of_not_ge hh
      have hcont : ContinuousAt (fun w => ‖F w-q‖) (c t) := (hF.continuousAt.sub continuousAt_const).norm
      have he : (radialTruncation H q r ∘ F) =ᶠ[𝓝 (c t)]
          (fun w => (1/2:ℝ)*Real.log (‖F w-q‖^2)-Real.log r) := by
        filter_upwards [continuousAt_const.eventually_lt hcont hl',
          hcont.eventually_lt continuousAt_const hh'] with w hw hw'
        exact radialTruncation_middle hr hw hw'
      have hdiff : DifferentiableAt ℝ (radialTruncation H q r ∘ F) (c t) := by
        apply he.differentiableAt_iff.2
        exact (((((hF.restrictScalars ℝ).sub_const q).norm_sq (𝕜 := ℝ)).log
          (pow_ne_zero 2 (hr.trans hl').ne')).const_mul (1/2:ℝ)).sub_const (Real.log r)
      exact (hdiff.hasFDerivAt.comp_hasDerivAt t hc).deriv

lemma acl_interval_energy {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hD : MemLp (deriv f) 2 (volume.restrict (Ioc a b))) :
    (f b-f a)^2 ≤ (b-a)*(∫ s in a..b, (deriv f s)^2) := by
  have hc := integral_mul_square_le hD (memLp_const (1:ℝ))
  have he : (∫ s in Ioc a b, deriv f s*1) = f b-f a := by
    simp only [mul_one,← intervalIntegral.integral_of_le hab,hf.integral_deriv_eq_sub]
  have he1 : (∫ s in Ioc a b, (1:ℝ)^2) = b-a := by simp [hab]
  rw [he,he1] at hc
  simpa only [intervalIntegral.integral_of_le hab,mul_comm] using hc

lemma weighted_acl_interval_energy {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hD : MemLp (fun s => Real.sqrt s*deriv f s) 2 (volume.restrict (Ioc a b))) :
    (f b-f a)^2 ≤ Real.log (b/a)*(∫ s in a..b, s*(deriv f s)^2) := by
  let g := fun s : ℝ => (Real.sqrt s)⁻¹
  have hs (s : ℝ) (hs : s ∈ Icc a b) : 0 < s := ha.trans_le hs.1
  have hg : ContinuousOn g (Icc a b) := Real.continuous_sqrt.continuousOn.inv₀
    (fun s hs' => (Real.sqrt_pos.2 (hs s hs')).ne')
  have hc := integral_mul_square_le hD (continuousOn_memLp_two_Ioc hab hg)
  have hfg : (∫ s in Ioc a b, (Real.sqrt s*deriv f s)*g s) = f b-f a := by
    calc
      _ = ∫ s in a..b, deriv f s := by
        rw [intervalIntegral.integral_of_le hab]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro s hs'
        dsimp [g]
        have hne := (Real.sqrt_pos.2 (hs s (Ioc_subset_Icc_self hs'))).ne'
        field_simp
      _ = _ := hf.integral_deriv_eq_sub
  have hff : (∫ s in Ioc a b, (Real.sqrt s*deriv f s)^2) =
      ∫ s in a..b, s*(deriv f s)^2 := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs'
    dsimp only
    rw [mul_pow,Real.sq_sqrt (hs s (Ioc_subset_Icc_self hs')).le]
  have hgg : (∫ s in Ioc a b, g s^2) = Real.log (b/a) := by
    calc
      _ = ∫ s in a..b, s⁻¹ := by
        rw [intervalIntegral.integral_of_le hab]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro s hs'
        dsimp only [g]
        rw [inv_pow,Real.sq_sqrt (hs s (Ioc_subset_Icc_self hs')).le]
      _ = _ := by
        apply integral_inv
        rw [uIcc_of_le hab]
        intro hz
        exact (not_le_of_gt ha) hz.1
  rw [hfg,hff,hgg] at hc
  simpa only [mul_comm] using hc

lemma lipschitzOn_deriv_memLp {a b : ℝ} {K : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzOnWith K f (Icc a b)) :
    MemLp (deriv f) 2 (volume.restrict (Ioc a b)) := by
  apply MemLp.of_bound (measurable_deriv f).aestronglyMeasurable (K:ℝ)
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    (ae_restrict_of_ae (μ := volume) (volume.ae_ne b))] with s hs hsb
  have hsl : s ∈ Ioo a b := ⟨hs.1,lt_of_le_of_ne hs.2 hsb⟩
  exact norm_deriv_le_of_lipschitzOn (mem_of_superset (isOpen_Ioo.mem_nhds hsl) Ioo_subset_Icc_self) hf

lemma lipschitzOn_weighted_deriv_memLp {a b : ℝ} {K : ℝ≥0} {f : ℝ → ℝ}
    (ha : 0 < a) (hf : LipschitzOnWith K f (Icc a b)) :
    MemLp (fun s => Real.sqrt s*deriv f s) 2 (volume.restrict (Ioc a b)) := by
  apply (lipschitzOn_deriv_memLp hf).of_le_mul
    ((Real.continuous_sqrt.measurable).mul (measurable_deriv f)).aestronglyMeasurable (c := Real.sqrt b)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Pi.mul_apply,norm_mul,Real.norm_of_nonneg (Real.sqrt_pos.2 (ha.trans hs.1)).le]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hs.2) (norm_nonneg _)

lemma truncated_curve_weighted_energy {H r a b : ℝ} (hr : 0 < r)
    (ha : 0 < a) (hab : a ≤ b) (q : ℂ) {G : ℝ → ℂ}
    (hG : ContDiffOn ℝ 1 G (Icc a b)) :
    (radialTruncation H q r (G b)-radialTruncation H q r (G a))^2 ≤
      Real.log (b/a)*(∫ s in a..b, s*(deriv (radialTruncation H q r ∘ G) s)^2) := by
  obtain ⟨K,hK⟩ := hG.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  have hL := (radialTruncation_lipschitz hr H q).comp_lipschitzOnWith hK
  exact weighted_acl_interval_energy ha hab
    (radialTruncation_along_C1_AC hr H q (by simpa only [uIcc_of_le hab] using hG))
    (lipschitzOn_weighted_deriv_memLp ha hL)

lemma mean_difference_square_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {u : α → ℝ} {v : β → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 ν) :
    ((∫ x, u x ∂μ)-(∫ y, v y ∂ν))^2 ≤
      ∫ x, ∫ y, (u x-v y)^2 ∂ν ∂μ := by
  have hD := (hu.comp_fst ν).sub (hv.comp_snd μ)
  have hc := integral_mul_square_le hD (memLp_const (1:ℝ))
  have hDi : Integrable (fun p : α × β => u p.1-v p.2) (μ.prod ν) :=
    hD.integrable (by norm_num)
  have he : (∫ p : α × β, (u p.1-v p.2)*1 ∂μ.prod ν) =
      (∫ x, u x ∂μ)-(∫ y, v y ∂ν) := by
    simp only [mul_one]
    rw [integral_prod _ hDi]
    have hiu := hu.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
    have hiv := hv.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
    simp_rw [integral_sub (integrable_const _) hiv]
    simp only [integral_const,probReal_univ,one_smul]
    rw [integral_sub hiu (integrable_const _)]
    simp
  have he1 : (∫ _ : α × β, (1:ℝ)^2 ∂μ.prod ν) = 1 := by simp
  simp only [Pi.sub_apply] at hc
  rw [he,he1,mul_one] at hc
  have hsq : Integrable (fun p : α × β => (u p.1-v p.2)^2) (μ.prod ν) := hD.integrable_sq
  rw [integral_prod _ hsq] at hc
  exact hc

lemma acl_oscillation_energy {a b : ℝ} {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hD : MemLp (deriv f) 2 (volume.restrict (Ioc a b)))
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (f y-f x)^2 ≤ (b-a)*(∫ s in a..b, (deriv f s)^2) := by
  have hab := hx.1.trans hx.2
  suffices ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      (f y-f x)^2 ≤ (b-a)*(∫ s in a..b, (deriv f s)^2) by
    rcases le_total x y with h | h
    · exact this x hx y hy h
    · have hh := this y hy x hx h
      nlinarith
  intro x hx y hy hxy
  have hsub : Ioc x y ⊆ Ioc a b := fun s hs => ⟨hx.1.trans_lt hs.1,hs.2.trans hy.2⟩
  have hD' := hD.mono_measure (Measure.restrict_mono_set _ hsub)
  have hf' : AbsolutelyContinuousOnInterval f x y := hf.mono
    (by simpa only [uIcc_of_le hab,uIcc_of_le hxy] using (Icc_subset_Icc hx.1 hy.2))
  have he := acl_interval_energy hxy hf' hD'
  have hmono : (∫ s in x..y, (deriv f s)^2) ≤ ∫ s in a..b, (deriv f s)^2 := by
    rw [intervalIntegral.integral_of_le hxy,intervalIntegral.integral_of_le hab]
    apply setIntegral_mono_set hD.integrable_sq
      (by filter_upwards with s; positivity) ?_
    exact ae_of_all _ (fun s hs => hsub hs)
  have hnon : 0 ≤ ∫ s in a..b, (deriv f s)^2 :=
    intervalIntegral.integral_nonneg hab (fun s hs => sq_nonneg _)
  exact he.trans ((mul_le_mul_of_nonneg_left hmono (sub_nonneg.2 hxy)).trans
    (mul_le_mul_of_nonneg_right (by linarith [hx.1,hy.2]) hnon))

lemma acl_congr {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (he : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ,hδ,hδ'⟩ := hf ε hε
  refine ⟨δ,hδ,?_⟩
  intro E hE hsum
  have hh := hδ' E hE hsum
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [he ((hE.1 i hi).1),he ((hE.1 i hi).2)]

lemma acl_of_interior {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hi : IntervalIntegrable (deriv f) volume a b)
    (hloc : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, AbsolutelyContinuousOnInterval f x y) :
    AbsolutelyContinuousOnInterval f a b := by
  let m := (a+b)/2
  have hm : m ∈ Ioo a b := by dsimp [m]; constructor <;> linarith
  let g := fun x => (∫ s in m..x, deriv f s)+f m
  have hg : AbsolutelyContinuousOnInterval g a b := by
    have hh := hi.absolutelyContinuousOnInterval_intervalIntegral
      (c := m) (by simpa only [uIcc_of_le hab.le] using Ioo_subset_Icc_self hm)
    have hk : AbsolutelyContinuousOnInterval (fun _ : ℝ => f m) a b :=
      (LipschitzWith.const (f m)).lipschitzOnWith.absolutelyContinuousOnInterval
    exact hh.add hk
  have he : EqOn f g (Ioo a b) := by
    intro x hx
    dsimp only [g]
    rw [(hloc m hm x hx).integral_deriv_eq_sub]
    ring
  have he' : EqOn f g (Icc a b) := he.of_subset_closure hc
    (by simpa only [uIcc_of_le hab.le] using hg.continuousOn)
    Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])
  exact acl_congr hg (by simpa only [uIcc_of_le hab.le] using he'.symm)

lemma boundary_zero_energy {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hD : MemLp (deriv f) 2 (volume.restrict (Ioc a b)))
    (hloc : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, AbsolutelyContinuousOnInterval f x y)
    {z : ℝ} (hz : z ∈ Icc a b) (hfz : f z = 0) {y : ℝ} (hy : y ∈ Icc a b) :
    (f y)^2 ≤ (b-a)*(∫ s in a..b, (deriv f s)^2) := by
  have hi : IntervalIntegrable (deriv f) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 (hD.integrable (by norm_num))
  have h := acl_oscillation_energy (acl_of_interior hab hc hi hloc) hD hz hy
  simpa only [hfz,sub_zero] using h

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace SLEExactGauge.Layer

lemma compact_parameter_derivative {F F' : ℝ → ℝ → ℝ} {a b l h x : ℝ}
    (hab : a ≤ b) (hlx : l < x) (hxh : x < h)
    (hF : ContinuousOn (Function.uncurry F) (Icc l h ×ˢ Icc a b))
    (hF' : ContinuousOn (Function.uncurry F') (Icc l h ×ˢ Icc a b))
    (hd : ∀ t ∈ Icc a b, ∀ y ∈ Icc l h, HasDerivAt (fun y => F y t) (F' y t) y) :
    HasDerivAt (fun y => ∫ t in a..b, F y t) (∫ t in a..b, F' x t) x := by
  have hc (y : ℝ) (hy : y ∈ Icc l h) : ContinuousOn (F y) (Icc a b) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hy,ht⟩)
  have hc' (y : ℝ) (hy : y ∈ Icc l h) : ContinuousOn (F' y) (Icc a b) :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hy,ht⟩)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF'
  have hxx : x ∈ Icc l h := ⟨hlx.le,hxh.le⟩
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Icc l h) (F' := F') (bound := fun _ => C) (Icc_mem_nhds hlx hxh) ?_
    (by apply ContinuousOn.intervalIntegrable; simpa only [uIcc_of_le hab] using hc x hxx)
    ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards [Icc_mem_nhds hlx hxh] with y hy
    have hh := ((hc y hy).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc
    simpa only [uIoc_of_le hab] using hh
  · have hh := ((hc' x hxx).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc
    simpa only [uIoc_of_le hab] using hh
  · filter_upwards with t ht y hy
    exact hC (y,t) ⟨hy,Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using ht)⟩
  · filter_upwards with t ht y hy
    exact hd t (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using ht)) y hy

lemma rotated_trace (H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (v : ℂ) (hv : ‖v‖ = 1) :
    H v v + H (Complex.I*v) (Complex.I*v) = H 1 1 + H Complex.I Complex.I := by
  have he : v = v.re • (1:ℂ) + v.im • Complex.I := by
    simp only [Complex.real_smul, mul_one]
    exact (Complex.re_add_im v).symm
  have hi : Complex.I*v = (-v.im) • (1:ℂ) + v.re • Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  have hh : v.re^2+v.im^2 = 1 := by
    have hsq := Complex.sq_norm v
    rw [hv,one_pow,Complex.normSq_apply] at hsq
    linarith
  calc
    _ = H (v.re • (1:ℂ) + v.im • Complex.I) (v.re • (1:ℂ) + v.im • Complex.I) +
        H ((-v.im) • (1:ℂ) + v.re • Complex.I) ((-v.im) • (1:ℂ) + v.re • Complex.I) := by
      rw [← he,← hi]
    _ = (v.re^2+v.im^2)*(H 1 1+H Complex.I Complex.I) := by
      simp only [map_add,map_smul,add_apply,smul_apply,
        smul_eq_mul]
      ring
    _ = _ := by rw [hh,one_mul]

lemma laplacian_eq_hessian (u : ℂ → ℝ) (z : ℂ) :
    Laplacian.laplacian u z =
      fderiv ℝ (fderiv ℝ u) z 1 1 + fderiv ℝ (fderiv ℝ u) z Complex.I Complex.I := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one]

lemma path_second {u : ℂ → ℝ} {c c' : ℝ → ℂ} {c'' : ℂ} {t : ℝ}
    (hu : ContDiffAt ℝ 2 u (c t)) (hc : HasDerivAt c (c' t) t)
    (hc' : HasDerivAt c' c'' t) :
    HasDerivAt (fun s => fderiv ℝ u (c s) (c' s))
      (fderiv ℝ (fderiv ℝ u) (c t) (c' t) (c' t) + fderiv ℝ u (c t) c'') t := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ u) (c t) := hu.fderiv_right (by norm_num)
  exact (hd.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hc |>.clm_apply hc'

def circleMean (u : ℂ → ℝ) (r : ℝ) : ℝ :=
  ∫ θ in -Real.pi..Real.pi, u (r • circleMap 0 1 θ)

def circleDMean (u : ℂ → ℝ) (r : ℝ) : ℝ :=
  ∫ θ in -Real.pi..Real.pi, fderiv ℝ u (r • circleMap 0 1 θ) (circleMap 0 1 θ)

def circleDDMean (u : ℂ → ℝ) (r : ℝ) : ℝ :=
  ∫ θ in -Real.pi..Real.pi,
    fderiv ℝ (fderiv ℝ u) (r • circleMap 0 1 θ) (circleMap 0 1 θ) (circleMap 0 1 θ)

lemma radial_norm (r θ : ℝ) : ‖r • circleMap 0 1 θ‖ = |r| := by
  simp [norm_circleMap_zero,Real.norm_eq_abs]

lemma radial_mem {r : ℝ} (hr : |r| < 1) (θ : ℝ) :
    r • circleMap 0 1 θ ∈ ball (0:ℂ) 1 := by
  rwa [mem_ball_zero_iff,radial_norm]

lemma radial_continuous : Continuous (fun p : ℝ × ℝ => p.1 • circleMap 0 1 p.2) :=
  continuous_fst.smul ((continuous_circleMap 0 1).comp continuous_snd)

lemma radial_interval_maps {l h a b : ℝ} (hl : -1 < l) (hh : h < 1) :
    MapsTo (fun p : ℝ × ℝ => p.1 • circleMap 0 1 p.2)
      (Icc l h ×ˢ Icc a b) (ball (0:ℂ) 1) := by
  rintro ⟨r,θ⟩ ⟨hr,hθ⟩
  exact radial_mem (abs_lt.2 ⟨hl.trans_le hr.1,hr.2.trans_lt hh⟩) θ

lemma circle_means_derivatives {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ 2 u (ball 0 1)) {r : ℝ} (hr : |r| < 1) :
    HasDerivAt (circleMean u) (circleDMean u r) r ∧
    HasDerivAt (circleDMean u) (circleDDMean u r) r := by
  have hr' := abs_lt.1 hr
  let l := (r-1)/2
  let h := (r+1)/2
  have hl : -1 < l := by dsimp [l]; linarith
  have hh : h < 1 := by dsimp [h]; linarith
  have hlr : l < r := by dsimp [l]; linarith
  have hrh : r < h := by dsimp [h]; linarith
  let K := Icc l h ×ˢ Icc (-Real.pi) Real.pi
  have hm : MapsTo (fun p : ℝ × ℝ => p.1 • circleMap 0 1 p.2) K (ball (0:ℂ) 1) :=
    radial_interval_maps hl hh
  have hdu : ContDiffOn ℝ 1 (fderiv ℝ u) (ball 0 1) :=
    hu.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hddu : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ u)) (ball 0 1) :=
    hdu.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hE : Continuous (fun p : ℝ × ℝ => circleMap 0 1 p.2) :=
    (continuous_circleMap 0 1).comp continuous_snd
  have h0 : ContinuousOn (fun p : ℝ × ℝ => u (p.1 • circleMap 0 1 p.2)) K :=
    hu.continuousOn.comp radial_continuous.continuousOn hm
  have h1 : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ u (p.1 • circleMap 0 1 p.2) (circleMap 0 1 p.2)) K :=
    (hdu.continuousOn.comp radial_continuous.continuousOn hm).clm_apply hE.continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ =>
      fderiv ℝ (fderiv ℝ u) (p.1 • circleMap 0 1 p.2) (circleMap 0 1 p.2) (circleMap 0 1 p.2)) K :=
    ((hddu.continuousOn.comp radial_continuous.continuousOn hm).clm_apply hE.continuousOn).clm_apply hE.continuousOn
  constructor
  · apply compact_parameter_derivative
      (F := fun s θ => u (s • circleMap 0 1 θ))
      (F' := fun s θ => fderiv ℝ u (s • circleMap 0 1 θ) (circleMap 0 1 θ))
      (neg_le_self Real.pi_pos.le) hlr hrh h0 h1
    intro θ hθ s hs
    have hmem := hm (show (s,θ) ∈ K from ⟨hs,hθ⟩)
    exact ((hu.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hmem)).hasFDerivAt.comp_hasDerivAt s
      (by simpa using (hasDerivAt_id s).smul_const (circleMap 0 1 θ))
  · apply compact_parameter_derivative
      (F := fun s θ => fderiv ℝ u (s • circleMap 0 1 θ) (circleMap 0 1 θ))
      (F' := fun s θ => fderiv ℝ (fderiv ℝ u) (s • circleMap 0 1 θ) (circleMap 0 1 θ) (circleMap 0 1 θ))
      (neg_le_self Real.pi_pos.le) hlr hrh h1 h2
    intro θ hθ s hs
    have hmem := hm (show (s,θ) ∈ K from ⟨hs,hθ⟩)
    have huc := hu.contDiffAt (isOpen_ball.mem_nhds hmem)
    have hd := path_second (c := fun t => t • circleMap 0 1 θ) (c' := fun _ => circleMap 0 1 θ)
      huc (by simpa using (hasDerivAt_id s).smul_const (circleMap 0 1 θ))
      (hasDerivAt_const s (circleMap 0 1 θ))
    simpa only [map_zero,add_zero] using hd

lemma circle_laplacian_continuous {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ 2 u (ball 0 1)) {r : ℝ} (hr : |r| < 1) :
    Continuous (fun θ => Laplacian.laplacian u (r • circleMap 0 1 θ)) := by
  have hc := (hu.fderiv_of_isOpen isOpen_ball (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).fderiv_of_isOpen
    isOpen_ball (show (0:WithTop ℕ∞)+1 ≤ 1 by norm_num)
  have hmaps : MapsTo (fun θ => r • circleMap 0 1 θ) univ (ball (0:ℂ) 1) := fun θ _ => radial_mem hr θ
  have hc' : Continuous (fun θ => fderiv ℝ (fderiv ℝ u) (r • circleMap 0 1 θ)) :=
    continuousOn_univ.1 (hc.continuousOn.comp ((continuous_circleMap 0 1).const_smul r).continuousOn hmaps)
  simp_rw [laplacian_eq_hessian]
  exact (hc'.clm_apply continuous_const |>.clm_apply continuous_const).add
    (hc'.clm_apply continuous_const |>.clm_apply continuous_const)

lemma circle_angular_laplacian {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ 2 u (ball 0 1)) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    r * (∫ θ in -Real.pi..Real.pi, Laplacian.laplacian u (r • circleMap 0 1 θ)) =
      circleDMean u r + r*circleDDMean u r := by
  have hrabs : |r| < 1 := by rwa [abs_of_pos hr]
  let E : ℝ → ℂ := circleMap 0 1
  let c : ℝ → ℂ := fun θ => r • E θ
  let H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ u)
  let J : ℝ → ℝ := fun θ => H (c θ) (E θ*Complex.I) (E θ*Complex.I)
  let D : ℝ → ℝ := fun θ => fderiv ℝ u (c θ) (E θ)
  let Q : ℝ → ℝ := fun θ => H (c θ) (E θ) (E θ)
  have hc : Continuous c := (continuous_circleMap 0 1).const_smul r
  have hEm : Continuous E := continuous_circleMap 0 1
  have hmem (θ : ℝ) : c θ ∈ ball (0:ℂ) 1 := radial_mem hrabs θ
  have hdu : ContDiffOn ℝ 1 (fderiv ℝ u) (ball 0 1) :=
    hu.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hddu : ContDiffOn ℝ 0 H (ball 0 1) :=
    hdu.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hdc : Continuous (fun θ => fderiv ℝ u (c θ)) :=
    continuousOn_univ.1 (hdu.continuousOn.comp hc.continuousOn (fun θ _ => hmem θ))
  have hHc : Continuous (fun θ => H (c θ)) :=
    continuousOn_univ.1 (hddu.continuousOn.comp hc.continuousOn (fun θ _ => hmem θ))
  have hD : Continuous D := hdc.clm_apply hEm
  have hJ : Continuous J := (hHc.clm_apply (hEm.mul_const Complex.I)).clm_apply (hEm.mul_const Complex.I)
  have hQ : Continuous Q := (hHc.clm_apply hEm).clm_apply hEm
  let V : ℝ → ℝ := fun θ => fderiv ℝ u (c θ) (r • (E θ*Complex.I))
  have hdV (θ : ℝ) : HasDerivAt V (r^2*J θ-r*D θ) θ := by
    have hcp : HasDerivAt c (r • (E θ*Complex.I)) θ := (hasDerivAt_circleMap 0 1 θ).const_smul r
    have hcpp : HasDerivAt (fun t => r • (E t*Complex.I)) (-(c θ)) θ := by
      have hh := ((hasDerivAt_circleMap 0 1 θ).mul_const Complex.I).const_smul r
      simpa only [Pi.smul_apply,E,c,mul_assoc,Complex.I_mul_I,mul_neg_one,smul_neg] using! hh
    have hh := path_second (hu.contDiffAt (isOpen_ball.mem_nhds (hmem θ))) hcp hcpp
    convert hh using 1
    dsimp only [H,J,D]
    simp only [map_smul,smul_apply,smul_eq_mul,map_neg]
    change r^2*((H (c θ)) (E θ*Complex.I)) (E θ*Complex.I)-r*(fderiv ℝ u (c θ)) (E θ) =
      r*(r*((H (c θ)) (E θ*Complex.I)) (E θ*Complex.I))-(fderiv ℝ u (c θ)) (r • E θ)
    rw [map_smul,smul_eq_mul]
    ring
  have hEnds : E (-Real.pi) = E Real.pi := by
    simp [E,circleMap,Complex.exp_neg_pi_mul_I,Complex.exp_pi_mul_I]
  have hVeq : V Real.pi = V (-Real.pi) := by
    dsimp only [V,c]
    rw [hEnds]
  have hz := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hdV θ)
    (((hJ.const_mul (r^2)).sub (hD.const_mul r)).intervalIntegrable (-Real.pi) Real.pi)
  rw [hVeq,sub_self] at hz
  rw [intervalIntegral.integral_sub ((hJ.intervalIntegrable _ _).const_mul _) ((hD.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hz
  have htrace (θ : ℝ) : Laplacian.laplacian u (c θ) = Q θ+J θ := by
    rw [laplacian_eq_hessian]
    symm
    convert rotated_trace (H (c θ)) (E θ) (by simp [E,norm_circleMap_zero]) using 1
    simp only [Q,J,H,mul_comm Complex.I]
  have hli : (∫ θ in -Real.pi..Real.pi, Laplacian.laplacian u (c θ)) =
      circleDDMean u r + ∫ θ in -Real.pi..Real.pi, J θ := by
    calc
      _ = ∫ θ in -Real.pi..Real.pi, Q θ+J θ := intervalIntegral.integral_congr (fun θ _ => htrace θ)
      _ = _ := intervalIntegral.integral_add (hQ.intervalIntegrable _ _) (hJ.intervalIntegrable _ _)
  change r*(∫ θ in -Real.pi..Real.pi, Laplacian.laplacian u (c θ)) = _
  rw [hli]
  change r^2*(∫ θ in -Real.pi..Real.pi, J θ)-r*circleDMean u r = 0 at hz
  nlinarith

lemma weighted_circle_derivative {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ 2 u (ball 0 1)) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun s => s*circleDMean u s)
      (r*(∫ θ in -Real.pi..Real.pi, Laplacian.laplacian u (r • circleMap 0 1 θ))) r := by
  have hd := (hasDerivAt_id r).mul (circle_means_derivatives hu (by rwa [abs_of_pos hr])).2
  simpa only [Pi.mul_apply,id_eq,one_mul,circle_angular_laplacian hu hr hr1] using! hd

lemma compact_parameter_continuousAt {F : ℝ → ℝ → ℝ} {a b l h x : ℝ}
    (hab : a ≤ b) (hlx : l < x) (hxh : x < h)
    (hF : ContinuousOn (Function.uncurry F) (Icc l h ×ˢ Icc a b)) :
    ContinuousAt (fun y => ∫ t in a..b, F y t) x := by
  have hc (y : ℝ) (hy : y ∈ Icc l h) : ContinuousOn (F y) (Icc a b) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hy,ht⟩)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => C) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [Icc_mem_nhds hlx hxh] with y hy
    have hh := ((hc y hy).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc
    simpa only [uIoc_of_le hab] using hh
  · filter_upwards [Icc_mem_nhds hlx hxh] with y hy
    filter_upwards with t ht
    exact hC (y,t) ⟨hy,Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using ht)⟩
  · filter_upwards with t ht
    have ht' : t ∈ Icc a b := Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using ht)
    have hh : ContinuousOn (fun y => F y t) (Icc l h) :=
      hF.comp (continuous_id.prodMk continuous_const).continuousOn (fun y hy => ⟨hy,ht'⟩)
    exact hh.continuousAt (Icc_mem_nhds hlx hxh)

lemma laplacian_continuousOn {u : ℂ → ℝ} (hu : ContDiffOn ℝ 2 u (ball 0 1)) :
    ContinuousOn (Laplacian.laplacian u) (ball (0:ℂ) 1) := by
  have hc := ((hu.fderiv_of_isOpen isOpen_ball (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).fderiv_of_isOpen
    isOpen_ball (show (0:WithTop ℕ∞)+1 ≤ 1 by norm_num)).continuousOn
  have he : Laplacian.laplacian u = fun z =>
      fderiv ℝ (fderiv ℝ u) z 1 1 + fderiv ℝ (fderiv ℝ u) z Complex.I Complex.I :=
    funext (laplacian_eq_hessian u)
  rw [he]
  exact (hc.clm_apply continuousOn_const |>.clm_apply continuousOn_const).add
    (hc.clm_apply continuousOn_const |>.clm_apply continuousOn_const)

def circleLMean (u : ℂ → ℝ) (r : ℝ) : ℝ :=
  ∫ θ in -Real.pi..Real.pi, Laplacian.laplacian u (r • circleMap 0 1 θ)

lemma circle_lmean_continuous {u : ℂ → ℝ} (hu : ContDiffOn ℝ 2 u (ball 0 1)) :
    ContinuousOn (circleLMean u) (Ioo (-1:ℝ) 1) := by
  intro r hr
  let l := (r-1)/2
  let h := (r+1)/2
  have hl : -1 < l := by dsimp [l]; linarith [hr.1]
  have hh : h < 1 := by dsimp [h]; linarith [hr.2]
  have hlr : l < r := by dsimp [l]; linarith [hr.1]
  have hrh : r < h := by dsimp [h]; linarith [hr.2]
  apply ContinuousAt.continuousWithinAt
  apply compact_parameter_continuousAt (F := fun r θ => Laplacian.laplacian u (r • circleMap 0 1 θ))
    (neg_le_self Real.pi_pos.le) hlr hrh
  exact (laplacian_continuousOn hu).comp radial_continuous.continuousOn (radial_interval_maps hl hh)

end SLEExactGauge.Layer

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace SLEExactGauge.Layer

lemma polar_symm_circle (r θ : ℝ) :
    Complex.polarCoord.symm (r,θ) = r • circleMap 0 1 θ := by
  rw [Complex.polarCoord_symm_apply]
  simp only [circleMap_zero,Complex.ofReal_one,one_mul,Complex.real_smul,Complex.exp_ofReal_mul_I]

lemma polar_disk_lintegral_le (f : ℂ → ℝ≥0∞) :
    (∫⁻ z in ball (0:ℂ) 1, f z) ≤
      ∫⁻ r in Ioo (0:ℝ) 1, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * f (r • circleMap 0 1 θ) := by
  classical
  let g := (ball (0:ℂ) 1).indicator f
  have hp := Complex.lintegral_comp_polarCoord_symm g
  rw [← lintegral_indicator measurableSet_ball f,← hp]
  change (∫⁻ p, ENNReal.ofReal p.1 * g (Complex.polarCoord.symm p)
    ∂(volume.prod volume).restrict (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi)) ≤ _
  rw [← Measure.prod_restrict]
  apply (lintegral_prod_le _).trans
  have he : (fun r => ∫⁻ θ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal r * g (Complex.polarCoord.symm (r,θ))) =ᵐ[volume.restrict (Ioi (0:ℝ))]
      (Iio (1:ℝ)).indicator (fun r => ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * f (r • circleMap 0 1 θ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    by_cases h1 : r < 1
    · rw [indicator_of_mem (show r ∈ Iio (1:ℝ) from h1)]
      apply lintegral_congr
      intro θ
      rw [polar_symm_circle]
      dsimp only [g]
      rw [indicator_of_mem (radial_mem (by rwa [abs_of_pos hr0]) θ)]
    · rw [indicator_of_notMem (show r ∉ Iio (1:ℝ) from h1)]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards with θ
      have hn : r • circleMap 0 1 θ ∉ ball (0:ℂ) 1 := by
        simpa only [mem_ball_zero_iff,radial_norm,abs_of_pos hr0] using h1
      rw [polar_symm_circle]
      dsimp only [g]
      simp only [indicator_of_notMem hn,mul_zero,Pi.zero_apply]
  rw [lintegral_congr_ae he,lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  have hset : Iio (1:ℝ) ∩ Ioi (0:ℝ) = Ioo (0:ℝ) 1 := by ext r; simp [and_comm]
  rw [hset]

end SLEExactGauge.Layer

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy
open Layer

lemma polar_annulus_lintegral_le (f : ℂ → ℝ≥0∞) {r R : ℝ} (hr : 0 < r) :
    (∫⁻ z in {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}, f z) ≤
      ∫⁻ s in Ioo r R, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal s*f (s • circleMap 0 1 θ) := by
  classical
  let A := {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  let g := A.indicator f
  have hp := Complex.lintegral_comp_polarCoord_symm g
  rw [← lintegral_indicator hA f,← hp]
  change (∫⁻ p, ENNReal.ofReal p.1*g (Complex.polarCoord.symm p)
    ∂(volume.prod volume).restrict (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi)) ≤ _
  rw [← Measure.prod_restrict]
  apply (lintegral_prod_le _).trans
  have he : (fun s => ∫⁻ θ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal s*g (Complex.polarCoord.symm (s,θ))) =ᵐ[volume.restrict (Ioi (0:ℝ))]
      (Ioo r R).indicator (fun s => ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal s*f (s • circleMap 0 1 θ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hs
    by_cases hh : s ∈ Ioo r R
    · rw [indicator_of_mem hh]
      apply lintegral_congr
      intro θ
      rw [polar_symm_circle]
      have hm : s • circleMap 0 1 θ ∈ A := by
        simpa only [A,mem_ofPred_eq,mem_Ioo,radial_norm,abs_of_pos hs0] using hh
      rw [show g (s • circleMap 0 1 θ) = f (s • circleMap 0 1 θ) by exact indicator_of_mem hm f]
    · rw [indicator_of_notMem hh]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards with θ
      have hn : s • circleMap 0 1 θ ∉ A := by
        simpa only [A,mem_ofPred_eq,mem_Ioo,radial_norm,abs_of_pos hs0] using hh
      rw [polar_symm_circle]
      dsimp only [g]
      simp only [indicator_of_notMem hn,mul_zero,Pi.zero_apply]
  rw [lintegral_congr_ae he,lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo]
  have hset : Ioo r R ∩ Ioi (0:ℝ) = Ioo r R :=
    inter_eq_left.2 (fun _ hs => hr.trans hs.1)
  rw [hset]

end SLEExactGauge.RectangleEnergy

end

end

end OAI
