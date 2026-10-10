import OAI.Geometry.Riemannian.HarmonicCore.Warping

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution
open Matrix
open scoped RealInnerProductSpace

namespace HarmonicCounterexample
lemma tailPrimitive_tendsto {J : ℝ} (hJ : 0 < J) :
    Tendsto (tailPrimitive J) atTop (𝓝 (tailMass J)) := by
  have hl := (tendsto_const_nhds (x := tailMass J)).sub
    ((tendsto_rpow_neg_atTop (by norm_num : 0 < (1/2 : ℝ))).const_mul 2)
  have he : (fun t : ℝ ↦ tailMass J - 2 * t ^ (-(1/2 : ℝ))) =ᶠ[atTop]
      tailPrimitive J := by
    filter_upwards [eventually_ge_atTop ((7/10 : ℝ) * J)] with t ht
    exact (tailPrimitive_exact hJ ht).symm
  simpa using hl.congr' he

lemma radialPrimitive_tendsto {J : ℝ} (hJ : 0 < J) :
    Tendsto (radialPrimitive J) atTop (𝓝 (tailMass J)) := by
  apply ((tailPrimitive_tendsto hJ).comp Real.tendsto_log_atTop).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  simp only [Function.comp_def, radialPrimitive, not_le.mpr hr, ↓reduceIte]

lemma sigma_tendsto : Tendsto sigma atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (7/4 : ℝ)] with r hr
  exact (sigma_one hr).symm

lemma slope_tendsto {C J : ℝ} (hJ : 0 < J) :
    Tendsto (slope C J) atTop (𝓝 a) := by
  have hl := ((tendsto_const_nhds (x := (1 : ℝ))).sub (sigma_tendsto.const_mul (compactLoss C J))).sub
    ((radialPrimitive_tendsto hJ).const_mul C)
  have he : 1 - compactLoss C J * 1 - C * tailMass J = a := by
    unfold compactLoss
    ring
  change Tendsto (fun r : ℝ ↦ 1 - compactLoss C J * sigma r - C * radialPrimitive J r) atTop (𝓝 a)
  simpa only [he] using hl

lemma compactLoss_eventually_pos (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ J : ℝ in atTop, 0 < compactLoss C J := by
  have hl : Tendsto (fun J : ℝ ↦ 2*C*(J/2)^(-(1/2 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : 0 < (1/2 : ℝ))).comp
      (Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2) tendsto_id)).const_mul (2*C)
  have hs := hl.eventually_lt_const (by norm_num [a] : 0 < 1 - a)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hs] with J hJ hbound
  have hm := mul_le_mul_of_nonneg_left (tailMass_bound hJ) hC
  dsimp [compactLoss]
  nlinarith

lemma warping_upper_tangent {C J R r : ℝ} (hJ : 0 < J) (hC : 0 ≤ C)
    (hm : 0 ≤ compactLoss C J) (hR : 0 ≤ R) (hr : R ≤ r) :
    warping C J r ≤ R + r * slope C J R := by
  have hs := intervalIntegral.integral_add_adjacent_intervals
    ((slope_smooth (C := C) hJ).continuous.intervalIntegrable (μ := volume) 0 R)
    ((slope_smooth (C := C) hJ).continuous.intervalIntegrable (μ := volume) R r)
  have hi := intervalIntegral.integral_mono_on hr
    ((slope_smooth (C := C) hJ).continuous.intervalIntegrable (μ := volume) R r)
    (intervalIntegrable_const)
    (fun x hx ↦ slope_antitone hJ hC hm hx.1)
  have hzero : 0 ≤ slope C J R := (by norm_num [a] : (0 : ℝ) ≤ a).trans (a_le_slope hJ hC hm R)
  have hbound := (warping_bounds hJ hC hm hR).2
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  change warping C J R + _ = warping C J r at hs
  nlinarith [mul_nonneg hR hzero]

lemma warping_ratio_tendsto {C J : ℝ} (hJ : 0 < J) (hC : 0 ≤ C)
    (hm : 0 ≤ compactLoss C J) :
    Tendsto (fun r : ℝ ↦ warping C J r / r) atTop (𝓝 a) := by
  apply tendsto_order.mpr
  constructor
  · intro l hl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact hl.trans_le ((le_div_iff₀ hr).2 (warping_bounds hJ hC hm hr.le).1)
  · intro u hu
    obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp ((slope_tendsto (C := C) hJ).eventually_lt_const hu)
    let R := max R₀ 1
    have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right R₀ 1)
    have hRu : slope C J R < u := hR₀ R (le_max_left R₀ 1)
    have hl : Tendsto (fun r : ℝ ↦ slope C J R + R / r) atTop (𝓝 (slope C J R)) := by
      simpa using (tendsto_const_nhds (x := slope C J R)).add
        ((tendsto_const_nhds (x := R)).div_atTop (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))
    filter_upwards [eventually_gt_atTop R, hl.eventually_lt_const hRu] with r hr hu'
    apply lt_of_le_of_lt _ hu'
    have hrpos := hR.trans hr
    apply (div_le_iff₀ hrpos).2
    have hid : (slope C J R + R / r) * r = R + r * slope C J R := by
      field_simp
      ring
    rw [hid]
    exact warping_upper_tangent hJ hC hm hR.le hr.le

lemma b_eq_div (C J t : ℝ) : b C J t = warping C J (Real.exp t) / Real.exp t := by
  simp only [b, Real.exp_neg, div_eq_mul_inv, mul_comm]

lemma b_bounds {C J : ℝ} (hJ : 0 < J) (hC : 0 ≤ C)
    (hm : 0 ≤ compactLoss C J) (t : ℝ) : a ≤ b C J t ∧ b C J t ≤ 1 := by
  rw [b_eq_div]
  have hr := Real.exp_pos t
  have hb := warping_bounds hJ hC hm hr.le
  constructor
  · exact (le_div_iff₀ hr).2 hb.1
  · exact (div_le_one hr).2 hb.2

lemma b_tendsto {C J : ℝ} (hJ : 0 < J) (hC : 0 ≤ C)
    (hm : 0 ≤ compactLoss C J) : Tendsto (b C J) atTop (𝓝 a) := by
  exact ((warping_ratio_tendsto hJ hC hm).comp Real.tendsto_exp_atTop).congr
    (fun t ↦ (b_eq_div C J t).symm)

lemma b_smooth {C J : ℝ} (hJ : 0 < J) : ContDiff ℝ ∞ (b C J) := by
  exact (Real.contDiff_exp.comp (contDiff_id.neg)).mul
    ((warping_smooth hJ).comp Real.contDiff_exp)

lemma b_hasDerivAt {C J : ℝ} (hJ : 0 < J) (t : ℝ) :
    HasDerivAt (b C J) (slope C J (Real.exp t) - b C J t) t := by
  have he := (hasDerivAt_id t).neg.exp
  have hf := (warping_hasDerivAt (C := C) hJ (Real.exp t)).comp t (Real.hasDerivAt_exp t)
  have hd := he.mul hf
  convert hd using 1 <;> try rfl
  simp only [b, Pi.neg_apply, id_eq, Function.comp_apply, Real.exp_neg]
  field_simp
  ring

lemma b_deriv {C J : ℝ} (hJ : 0 < J) :
    deriv (b C J) = fun t ↦ slope C J (Real.exp t) - b C J t := by
  funext t
  exact (b_hasDerivAt hJ t).deriv

lemma b_first_equation {C J : ℝ} (hJ : 0 < J) (t : ℝ) :
    deriv (b C J) t + b C J t = slope C J (Real.exp t) := by
  rw [b_deriv hJ]
  ring

lemma b_deriv_hasDerivAt {C J : ℝ} (hJ : 0 < J) (t : ℝ) :
    HasDerivAt (deriv (b C J))
      ((-compactLoss C J * beta (Real.exp t) - C * radialDensity J (Real.exp t)) *
        Real.exp t - deriv (b C J) t) t := by
  rw [b_deriv hJ]
  exact ((slope_hasDerivAt hJ (Real.exp t)).comp t (Real.hasDerivAt_exp t)).sub
    (b_hasDerivAt hJ t)

lemma b_second_deriv {C J : ℝ} (hJ : 0 < J) (t : ℝ) :
    deriv (deriv (b C J)) t =
      (-compactLoss C J * beta (Real.exp t) - C * radialDensity J (Real.exp t)) *
        Real.exp t - deriv (b C J) t :=
  (b_deriv_hasDerivAt hJ t).deriv

lemma slope_exp_exact {C J t : ℝ} (hJ : 4 ≤ J) (ht : (7/10 : ℝ)*J ≤ t) :
    slope C J (Real.exp t) = a + 2*C*t^(-(1/2 : ℝ)) := by
  have hJpos : 0 < J := by linarith
  have htpos : 0 < t := by linarith
  have hr : (7/4 : ℝ) < Real.exp t := by linarith [Real.add_one_le_exp t]
  have h1 : ¬Real.exp t ≤ 1 := by linarith
  simp only [slope, sigma_one hr.le, radialPrimitive, h1, ↓reduceIte,
    Real.log_exp, tailPrimitive_exact hJpos ht]
  unfold compactLoss
  ring

lemma b_first_equation_tail {C J t : ℝ} (hJ : 4 ≤ J) (ht : (7/10 : ℝ)*J ≤ t) :
    deriv (b C J) t + b C J t = a + 2*C*t^(-(1/2 : ℝ)) := by
  rw [b_first_equation (by linarith : 0 < J), slope_exp_exact hJ ht]

lemma b_second_equation {C J t : ℝ} (hJ : 4 ≤ J) (ht : (7/10 : ℝ)*J ≤ t) :
    deriv (deriv (b C J)) t + deriv (b C J) t = -C*t^(-(3/2 : ℝ)) := by
  have hJpos : 0 < J := by linarith
  have hr : (7/4 : ℝ) < Real.exp t := by linarith [Real.add_one_le_exp t]
  have he : Real.exp (J/2) < Real.exp t := Real.exp_lt_exp.mpr (by linarith)
  rw [b_second_deriv hJpos, beta_zero_right hr]
  simp only [radialDensity, he, ↓reduceIte, Real.log_exp,
    tailDensity_exact hJpos ht, mul_zero, zero_sub]
  field_simp
  ring

lemma b_deriv_bounded {C J : ℝ} (hJ : 0 < J) (hC : 0 ≤ C)
    (hm : 0 ≤ compactLoss C J) (t : ℝ) : |deriv (b C J) t| ≤ 1 - a := by
  rw [b_deriv hJ, abs_le]
  have hs1 := a_le_slope hJ hC hm (Real.exp t)
  have hs2 := slope_le_one hJ hC hm (Real.exp t)
  have hb := b_bounds hJ hC hm t
  constructor <;> linarith [hb.1, hb.2]

lemma slope_le_b {C J : ℝ} (hJ : 0 < J) (hC : 0 ≤ C)
    (hm : 0 ≤ compactLoss C J) (t : ℝ) : slope C J (Real.exp t) ≤ b C J t := by
  rw [b_eq_div, le_div_iff₀ (Real.exp_pos t)]
  have hi := (slope_smooth (C := C) hJ).continuous.intervalIntegrable
    (μ := volume) 0 (Real.exp t)
  have h := intervalIntegral.integral_mono_on (Real.exp_pos t).le
    intervalIntegrable_const hi (fun x hx ↦ slope_antitone hJ hC hm hx.2)
  simpa [warping, mul_comm] using h

lemma b_deriv_nonpos {C J : ℝ} (hJ : 0 < J) (hC : 0 ≤ C)
    (hm : 0 ≤ compactLoss C J) (t : ℝ) : deriv (b C J) t ≤ 0 := by
  rw [b_deriv hJ]
  exact sub_nonpos.mpr (slope_le_b hJ hC hm t)

end HarmonicCounterexample

end

end OAI
