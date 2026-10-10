import OAI.Analysis.NumericalRange.ExteriorKernel

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_30 u_31 u_32 u_33 u_34

open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real
section
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma unitAddCircle_integral_eq_circleAverage {E : Type u_30}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ t : UnitAddCircle, f (t.toCircle : ℂ) ∂AddCircle.haarAddCircle) =
      Real.circleAverage f 0 1 := by
  rw [AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage 1 0]
  simp only [inv_one, one_smul, zero_add]
  have he : (fun t : ℝ => f ((AddCircle.toCircle (T := 1) (t : UnitAddCircle)) : ℂ)) =
      (fun t : ℝ => f (circleMap 0 1 (2*Real.pi*t))) := by
    funext t
    congr 1
    simp only [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap,
      ofReal_one, one_mul, zero_add, div_one]
  rw [he, Real.circleAverage]
  have hpi : 2*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  simpa using intervalIntegral.integral_comp_mul_left
    (fun t : ℝ => f (circleMap 0 1 t)) hpi (a := 0) (b := 1)

lemma fourier_natCast_toCircle (n : ℕ) (t : UnitAddCircle) :
    fourier (n : ℤ) t = (t.toCircle : ℂ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, fourier_one, pow_succ]

lemma fourier_neg_natCast_toCircle (n : ℕ) (t : UnitAddCircle) :
    fourier (-(n : ℤ)) t = ((t.toCircle : ℂ)⁻¹)^n := by
  rw [fourier_neg, fourier_natCast_toCircle, map_pow]
  congr 1
  exact (Circle.coe_inv_eq_conj t.toCircle).symm.trans (Circle.coe_inv t.toCircle)

lemma integral_analytic_circle {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) :
    (∫ t : UnitAddCircle, f (t.toCircle : ℂ) ∂AddCircle.haarAddCircle) = f 0 := by
  rw [unitAddCircle_integral_eq_circleAverage]
  have hd : DiffContOnCl ℂ f (Metric.ball 0 |(1:ℝ)|) := by
    constructor
    · simp only [abs_one]
      exact hf.differentiableOn.mono Metric.ball_subset_closedBall
    · simpa only [abs_one, closure_ball (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)] using hf.continuousOn
  exact hd.circleAverage

lemma integral_analytic_mul_pow {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)^n * f (t.toCircle : ℂ)
      ∂AddCircle.haarAddCircle) = 0 := by
  simpa only [Pi.mul_apply, Pi.pow_apply, id_eq, zero_pow hn, zero_mul] using
    integral_analytic_circle ((analyticOnNhd_id.pow n).mul hf)

lemma integral_reciprocal_analytic_mul_inv_pow {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : UnitAddCircle, ((t.toCircle : ℂ)⁻¹)^n * f (t.toCircle : ℂ)⁻¹
      ∂AddCircle.haarAddCircle) = 0 := by
  rw [unitAddCircle_integral_eq_circleAverage
      (fun z => (z⁻¹)^n * f z⁻¹)]
  rw [Real.circleAverage_zero_one_congr_inv
      (f := fun z => z^n*f z)]
  rw [← unitAddCircle_integral_eq_circleAverage]
  exact integral_analytic_mul_pow hf hn

lemma integral_reciprocal_analytic {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) :
    (∫ t : UnitAddCircle, f (t.toCircle : ℂ)⁻¹
      ∂AddCircle.haarAddCircle) = f 0 := by
  rw [unitAddCircle_integral_eq_circleAverage (fun z => f z⁻¹),
    Real.circleAverage_zero_one_congr_inv,
    ← unitAddCircle_integral_eq_circleAverage]
  exact integral_analytic_circle hf

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology
section

lemma compact_parametric_hasDerivAt {α : Type u_31} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U)
    {f f' : ℂ → α → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf' : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hd : ∀ z ∈ U, ∀ t, HasDerivAt (fun w => f w t) (f' z t) z)
    {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w => ∫ t, f w t ∂μ) (∫ t, f' z t ∂μ) z := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  have hs : closedBall z (ε/2) ⊆ U := by
    exact (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨C,hC⟩ := (isCompact_closedBall z (ε/2)).prod isCompact_univ
    |>.exists_bound_of_continuousOn (hf'.mono (prod_mono hs (Subset.refl _)))
  have hc (w : ℂ) (hw : w ∈ U) : Continuous (f w) := by
    exact hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun t => ⟨hw,mem_univ t⟩)
  have hc' (w : ℂ) (hw : w ∈ U) : Continuous (f' w) := by
    exact hf'.comp_continuous (continuous_const.prodMk continuous_id)
      (fun t => ⟨hw,mem_univ t⟩)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := f) (F' := f') (bound := fun _ : α => C)
    (closedBall_mem_nhds z (by linarith : 0 < ε/2)) ?_ ?_ ?_ ?_ (integrable_const C) ?_).2
  · filter_upwards [hU.mem_nhds hz] with w hw
    exact (hc w hw).aestronglyMeasurable
  · exact (hc z hz).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hc' z hz).aestronglyMeasurable
  · filter_upwards [] with t
    intro w hw
    exact hC (w,t) ⟨hw,mem_univ t⟩
  · filter_upwards [] with t
    intro w hw
    exact hd w (hs hw) t

lemma analyticOnNhd_compact_integral {α : Type u_32} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U)
    {f f' : ℂ → α → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf' : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hd : ∀ z ∈ U, ∀ t, HasDerivAt (fun w => f w t) (f' z t) z) :
    AnalyticOnNhd ℂ (fun w => ∫ t, f w t ∂μ) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro z hz
  exact (compact_parametric_hasDerivAt hU hf hf' hd hz).differentiableAt.differentiableWithinAt

def physicalCauchy (G : ℂ → ℂ) (u : UnitAddCircle → ℂ) (z : ℂ) : ℂ :=
  ∫ t : UnitAddCircle, u t *
    ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-z))
    ∂AddCircle.haarAddCircle

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma physicalCauchy_analytic {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    {u : UnitAddCircle → ℂ} (hu : Continuous u) {U : Set ℂ} (hU : IsOpen U)
    (hne : ∀ z ∈ U, ∀ t : UnitAddCircle, G (t.toCircle : ℂ) ≠ z) :
    AnalyticOnNhd ℂ (physicalCauchy G u) U := by
  have hcc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle
  have hm (t : UnitAddCircle) : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 :=
    t.toCircle.property
  have hcG : Continuous (fun t : UnitAddCircle => G (t.toCircle : ℂ)) :=
    hG.continuousOn.comp_continuous hcc hm
  have hcdG : Continuous (fun t : UnitAddCircle => deriv G (t.toCircle : ℂ)) :=
    hG.deriv.continuousOn.comp_continuous hcc hm
  apply analyticOnNhd_compact_integral hU
    (f' := fun z t => u t*((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/
      (G (t.toCircle : ℂ)-z)^2))
  · exact (hu.comp continuous_snd).continuousOn.fun_mul
      (((hcc.comp continuous_snd).continuousOn.fun_mul
        (hcdG.comp continuous_snd).continuousOn).div
        ((hcG.comp continuous_snd).continuousOn.sub continuousOn_fst)
        (fun p hp => sub_ne_zero.mpr (hne p.1 hp.1 p.2)))
  · exact (hu.comp continuous_snd).continuousOn.fun_mul
      (((hcc.comp continuous_snd).continuousOn.fun_mul
        (hcdG.comp continuous_snd).continuousOn).div
        (((hcG.comp continuous_snd).continuousOn.sub continuousOn_fst).pow 2)
        (fun p hp => pow_ne_zero _ (sub_ne_zero.mpr (hne p.1 hp.1 p.2))))
  · intro z hz t
    have he := (((hasDerivAt_const z ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ))).fun_div
      ((hasDerivAt_id z).const_sub (G (t.toCircle : ℂ))) (sub_ne_zero.mpr (hne z hz t))).const_mul (u t))
    simpa only [id_eq, neg_neg, zero_mul, sub_neg_eq_add, zero_add, mul_one, mul_neg_one, zero_sub] using he

lemma unitAddCircle_integral_affine {E : Type u_33}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ) :
    (∫ t : UnitAddCircle, f (c+R*(t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) =
      Real.circleAverage f c R := by
  rw [unitAddCircle_integral_eq_circleAverage (fun z => f (c+R*z))]
  simp only [Real.circleAverage, circleMap, ofReal_one, one_mul, zero_add]

lemma analyticOnNhd_integral_of_continuous {α : Type u_34} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U) {f : ℂ → α → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (ha : ∀ t, AnalyticOnNhd ℂ (fun z => f z t) U) :
    AnalyticOnNhd ℂ (fun z => ∫ t, f z t ∂μ) U := by
  intro c hc
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hc)
  let R := ε/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed : closedBall c R ⊆ U :=
    (closedBall_subset_ball (by dsimp [R]; linarith : R < ε)).trans hεU
  let G : ℂ → ℂ := fun z => c+R*z
  have hG : AnalyticOnNhd ℂ G univ :=
    analyticOnNhd_const.add (analyticOnNhd_const.mul analyticOnNhd_id)
  have hcd (t : UnitAddCircle) : G (t.toCircle : ℂ) ∈ sphere c R := by
    change dist (c+R*(t.toCircle : ℂ)) c = R
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos hR, Circle.norm_coe, mul_one]
  have hcc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle
  have hGc : Continuous G := by fun_prop
  have hGc' : deriv G = fun _ => (R : ℂ) := by
    funext z
    exact ((hasDerivAt_id z).const_mul (R:ℂ) |>.const_add c).deriv.trans (by simp)
  have hne (z : ℂ) (hz : z ∈ ball c R) (t : UnitAddCircle) :
      G (t.toCircle : ℂ) ≠ z := by
    intro he
    have ht := hcd t
    rw [he] at ht
    exact ne_of_lt hz ht
  let u : UnitAddCircle → ℂ := fun t => ∫ a, f (G (t.toCircle : ℂ)) a ∂μ
  have hfu : Continuous (fun p : UnitAddCircle × α => f (G (p.1.toCircle : ℂ)) p.2) := by
    exact hf.comp_continuous ((hGc.comp (hcc.comp continuous_fst)).prodMk continuous_snd)
      (fun p => ⟨hclosed (sphere_subset_closedBall (hcd p.1)),mem_univ _⟩)
  have hu : Continuous u := by
    exact continuousOn_univ.mp (continuousOn_integral_of_compact_support
      (μ := μ) isCompact_univ hfu.continuousOn (fun _ _ _ h => (h (mem_univ _)).elim))
  have hka := physicalCauchy_analytic (hG.mono (subset_univ _)) hu isOpen_ball hne
  have he (w : ℂ) (hw : w ∈ ball c R) :
      physicalCauchy G u w = ∫ a, f w a ∂μ := by
    have hkt : Continuous (fun p : UnitAddCircle × α =>
        f (G (p.1.toCircle : ℂ)) p.2 *
          ((p.1.toCircle : ℂ)*deriv G (p.1.toCircle : ℂ)/(G (p.1.toCircle : ℂ)-w))) := by
      apply hfu.mul
      rw [hGc']
      exact (((hcc.comp continuous_fst).mul continuous_const).div
        ((hGc.comp (hcc.comp continuous_fst)).sub continuous_const)
        (fun p => sub_ne_zero.mpr (hne w hw p.1)))
    change (∫ t : UnitAddCircle, (∫ a, f (G (t.toCircle : ℂ)) a ∂μ) *
      ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-w))
      ∂AddCircle.haarAddCircle) = _
    simp_rw [← integral_mul_const]
    rw [integral_integral_swap (hkt.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
    apply integral_congr_ae
    filter_upwards [] with a
    have hdiff : DiffContOnCl ℂ (fun z => f z a) (ball c |R|) := by
      constructor
      · rw [abs_of_pos hR]
        exact (ha a).differentiableOn.mono (ball_subset_closedBall.trans hclosed)
      · simpa only [abs_of_pos hR, closure_ball c (ne_of_gt hR)] using
          ((ha a).mono hclosed).continuousOn
    have hw' : w ∈ ball c |R| := by simpa [abs_of_pos hR] using hw
    rw [hGc']
    have hi := unitAddCircle_integral_affine
      (fun z => ((z-c)/(z-w))*f z a) c R
    simp only [add_sub_cancel_left] at hi
    rw [show (fun t : UnitAddCircle => f (G (t.toCircle : ℂ)) a *
        ((t.toCircle : ℂ)*(R:ℂ)/(G (t.toCircle : ℂ)-w))) =
      (fun t => ((c+R*(t.toCircle : ℂ)-c)/(c+R*(t.toCircle : ℂ)-w))*
        f (c+R*(t.toCircle : ℂ)) a) by
      funext t; dsimp [G]; ring]
    erw [unitAddCircle_integral_affine (fun z => ((z-c)/(z-w))*f z a) c R]
    exact hdiff.circleAverage_smul_div hw'
  exact (hka c (mem_ball_self hR)).congr
    (Filter.eventuallyEq_iff_exists_mem.mpr ⟨ball c R,isOpen_ball.mem_nhds (mem_ball_self hR),he⟩)

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma circle_cauchy_pow (n : ℕ) {w : ℂ} (hw : w ∈ ball 0 1) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)^n *
      ((t.toCircle : ℂ)/((t.toCircle : ℂ)-w)) ∂AddCircle.haarAddCircle) = w^n := by
  have hd : DiffContOnCl ℂ (fun z : ℂ => z^n) (ball 0 |(1:ℝ)|) := by
    exact (analyticOnNhd_id.pow n).differentiableOn.diffContOnCl
  have hw' : w ∈ ball 0 |(1:ℝ)| := by simpa using hw
  have he := hd.circleAverage_smul_div hw'
  rw [← unitAddCircle_integral_eq_circleAverage] at he
  simpa only [sub_zero, smul_eq_mul, mul_comm] using he

lemma circle_cauchy_inv_pow {n : ℕ} (hn : n ≠ 0) {w : ℂ} (hw : w ∈ ball 0 1) :
    (∫ t : UnitAddCircle, ((t.toCircle : ℂ)⁻¹)^n *
      ((t.toCircle : ℂ)/((t.toCircle : ℂ)-w)) ∂AddCircle.haarAddCircle) = 0 := by
  have hnz (s : ℂ) (hs : s ∈ closedBall 0 1) : 1-w*s ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hnw : ‖w‖ < 1 := by simpa [mem_ball, dist_zero_right] using hw
    have hns : ‖s‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hs
    have hh : ‖w*s‖ < 1 := by
      rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hns) hnw
    rw [← he, norm_one] at hh
    exact (lt_irrefl 1) hh
  have ha : AnalyticOnNhd ℂ (fun s : ℂ => s^n/(1-w*s)) (closedBall 0 1) := by
    intro s hs
    exact (analyticAt_id.pow n).div (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
      (hnz s hs)
  have he := integral_reciprocal_analytic ha
  have hc : (fun t : UnitAddCircle => ((t.toCircle : ℂ)⁻¹)^n *
      ((t.toCircle : ℂ)/((t.toCircle : ℂ)-w))) =
      (fun t => ((t.toCircle : ℂ)⁻¹)^n/(1-w*(t.toCircle : ℂ)⁻¹)) := by
    funext t
    have ht : (t.toCircle : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have htw : (t.toCircle : ℂ)-w ≠ 0 := by
      apply sub_ne_zero.mpr
      intro ee
      have ht' := Circle.norm_coe t.toCircle
      rw [ee] at ht'
      have hw' : ‖w‖ < 1 := by simpa [mem_ball, dist_zero_right] using hw
      linarith
    field_simp
  rw [hc]
  simpa only [zero_pow hn, mul_zero, sub_zero, div_one] using he

def cauchyCorrectionIntegral (G : ℂ → ℂ) (u : UnitAddCircle → ℂ) (w : ℂ) : ℂ :=
  ∫ t : UnitAddCircle, u t * exteriorCorrection G w (t.toCircle : ℂ)
    ∂AddCircle.haarAddCircle

lemma cauchyCorrectionIntegral_analytic {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) (hTU : sphere 0 1 ⊆ U)
    {u : UnitAddCircle → ℂ} (hu : Continuous u) :
    AnalyticOnNhd ℂ (cauchyCorrectionIntegral G u) U := by
  have hcc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle
  have hp : Continuous (fun p : ℂ × UnitAddCircle => (p.1,(p.2.toCircle : ℂ))) :=
    continuous_fst.prodMk (hcc.comp continuous_snd)
  have hb : ContinuousOn (fun p : ℂ × UnitAddCircle =>
      exteriorCorrection G p.1 (p.2.toCircle : ℂ)) (U ×ˢ univ) :=
    ContinuousOn.comp (g := Function.uncurry (exteriorCorrection G))
      (f := fun p : ℂ × UnitAddCircle => (p.1,(p.2.toCircle : ℂ)))
      (s := U ×ˢ (univ : Set UnitAddCircle)) (t := U ×ˢ U)
      (exteriorCorrection_continuousOn hU hG hi hd) hp.continuousOn
      (fun p hp => ⟨hp.1,hTU p.2.toCircle.property⟩)
  exact analyticOnNhd_integral_of_continuous hU
    ((hu.comp continuous_snd).continuousOn.fun_mul hb)
    (fun t => analyticOnNhd_const.mul (exteriorCorrection_analytic_left hU hG hi hd
      (hTU t.toCircle.property)))

lemma physicalCauchy_decompose {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) (hTU : sphere 0 1 ⊆ U)
    {u : UnitAddCircle → ℂ} (hu : Continuous u) {w : ℂ}
    (hw : w ∈ U) (hwin : w ∈ ball 0 1) :
    physicalCauchy G u (G w) =
      (∫ t : UnitAddCircle, u t*((t.toCircle : ℂ)/((t.toCircle : ℂ)-w))
        ∂AddCircle.haarAddCircle) + cauchyCorrectionIntegral G u w := by
  have hcc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle
  have hne (t : UnitAddCircle) : (t.toCircle : ℂ) ≠ w := by
    intro he
    have ht := t.toCircle.property
    rw [he] at ht
    exact ne_of_lt hwin ht
  have hc1 : Continuous (fun t : UnitAddCircle =>
      u t*((t.toCircle : ℂ)/((t.toCircle : ℂ)-w))) :=
    hu.mul (hcc.div (hcc.sub continuous_const) (fun t => sub_ne_zero.mpr (hne t)))
  have hc2 : Continuous (fun t : UnitAddCircle =>
      u t*exteriorCorrection G w (t.toCircle : ℂ)) :=
    hu.mul ((exteriorCorrection_analytic_right hU hG hi hd hw).continuousOn.comp_continuous
      hcc (fun t => hTU t.toCircle.property))
  rw [physicalCauchy, cauchyCorrectionIntegral, ← integral_add
    (hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hc2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [exteriorCorrection_eq (hne t) (hG _ (hTU t.toCircle.property)).differentiableAt
    (fun he => hne t (hi (hTU t.toCircle.property) hw he))]
  ring

lemma physicalCauchy_pow {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) (hTU : sphere 0 1 ⊆ U)
    (n : ℕ) {w : ℂ} (hw : w ∈ U) (hwin : w ∈ ball 0 1) :
    physicalCauchy G (fun t => (t.toCircle : ℂ)^n) (G w) =
      w^n + cauchyCorrectionIntegral G (fun t => (t.toCircle : ℂ)^n) w := by
  erw [physicalCauchy_decompose hU hG hi hd hTU
    ((continuous_subtype_val.comp AddCircle.continuous_toCircle).pow n) hw hwin,
    circle_cauchy_pow n hwin]
  rfl

lemma physicalCauchy_inv_pow {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) (hTU : sphere 0 1 ⊆ U)
    {n : ℕ} (hn : n ≠ 0) {w : ℂ} (hw : w ∈ U) (hwin : w ∈ ball 0 1) :
    physicalCauchy G (fun t => ((t.toCircle : ℂ)⁻¹)^n) (G w) =
      cauchyCorrectionIntegral G (fun t => ((t.toCircle : ℂ)⁻¹)^n) w := by
  have hu : Continuous (fun t : UnitAddCircle => ((t.toCircle : ℂ)⁻¹)^n) :=
    ((continuous_subtype_val.comp AddCircle.continuous_toCircle).inv₀
      (fun t => Circle.coe_ne_zero _)).pow n
  rw [physicalCauchy_decompose hU hG hi hd hTU hu hw hwin,
    circle_cauchy_inv_pow hn hwin, zero_add]


end CompleteCrouzeix

end

end OAI
