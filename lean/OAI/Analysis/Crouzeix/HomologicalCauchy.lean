import Mathlib
import OAI.Analysis.Crouzeix.Definitions
import OAI.Analysis.Crouzeix.ResolventBounds
import OAI.Analysis.Crouzeix.ContourExistence

namespace OAI

/-! Homological Cauchy. -/

noncomputable section

open Set Filter Metric MeasureTheory

open scoped Topology

namespace CrouzeixHilbert

def extendCompactFunction {K : Set ℂ} {E : Type*} [TopologicalSpace E] [Zero E]
    (f : C(K, E)) (z : ℂ) : E := by
  classical
  exact if hz : z ∈ K then f ⟨z, hz⟩ else 0

@[simp]
theorem extendCompactFunction_apply {K : Set ℂ} {E : Type*}
    [TopologicalSpace E] [Zero E] (f : C(K, E)) {z : ℂ} (hz : z ∈ K) :
    (extendCompactFunction f) z = f ⟨z, hz⟩ := by
  classical
  simp only [extendCompactFunction, dite_eq_left hz]

def holomorphicContinuousFunctions (K : Set ℂ) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] : Submodule ℂ C(K, E) where
  carrier := {f | DifferentiableOn ℂ (extendCompactFunction f) (interior K)}
  zero_mem' := by
    apply (differentiableOn_const (c := (0 : E))).congr
    intro z hz
    simp only [extendCompactFunction_apply _ (interior_subset hz), ContinuousMap.zero_apply]
  add_mem' := by
    intro f g hf hg
    apply (hf.add hg).congr
    intro z hz
    simp only [extendCompactFunction_apply _ (interior_subset hz), ContinuousMap.add_apply, Pi.add_apply]
  smul_mem' := by
    intro c f hf
    apply (hf.const_smul c).congr
    intro z hz
    simp only [extendCompactFunction_apply _ (interior_subset hz), ContinuousMap.smul_apply, Pi.smul_apply]

theorem isClosed_holomorphicContinuousFunctions {K : Set ℂ} [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] :
    IsClosed (holomorphicContinuousFunctions K E : Set C(K, E)) := by
  apply IsSeqClosed.isClosed
  intro fs f hfs hf
  have ht : TendstoUniformlyOn (fun n => (extendCompactFunction (fs n))) (extendCompactFunction f) atTop (interior K) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hf ε hε] with n hn z hz
    simp only [extendCompactFunction_apply _ (interior_subset hz)]
    exact (ContinuousMap.dist_apply_le_dist (f := f) (g := fs n) (⟨z, interior_subset hz⟩ : K)).trans_lt (by simpa [dist_comm] using hn)
  exact ht.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall hfs) isOpen_interior

theorem differentiableOn_parameter_intervalIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ → E}
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ Icc (0 : ℝ) 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun z => f z t) U) :
    DifferentiableOn ℂ (fun z => ∫ t in (0 : ℝ)..1, f z t) U := by
  classical
  intro z hz
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  let K := closedBall z r
  have hKc : IsCompact K := isCompact_closedBall z r
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let g : ℝ → C(K, E) := fun t => if ht : t ∈ Icc (0 : ℝ) 1 then
    ⟨fun w => f w t, ((hd t ht).continuousOn.mono hrU).domRestrict⟩ else 0
  have hga (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (w : K) : g t w = f w t := by
    simp only [g, dite_eq_left ht]
    rfl
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hc : Continuous (fun p : ↥(Icc (0 : ℝ) 1) × K =>
        f p.2 p.1) := hf.comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst))
      (fun p => ⟨hrU p.2.property, p.1.property⟩)
    convert! hc using 1
    funext p
    exact hga p.1 p.1.property p.2
  have hgi : IntervalIntegrable g volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using hg
  let S := holomorphicContinuousFunctions K E
  have hgm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t ∈ S := by
    change DifferentiableOn ℂ (extendCompactFunction (g t)) (interior K)
    apply ((hd t ht).mono (interior_subset.trans hrU)).congr
    intro w hw
    rw [extendCompactFunction_apply _ (interior_subset hw), hga t ht]
  have hmi : (∫ t in (0 : ℝ)..1, g t) ∈ S := by
    have : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact (S.restrictScalars ℝ).convex.integral_mem isClosed_holomorphicContinuousFunctions
      ((ae_restrict_mem measurableSet_Ioc).mono
        (fun t ht => hgm t (Ioc_subset_Icc_self ht))) hgi.1
  have hdint : DifferentiableOn ℂ (fun w => ∫ t in (0 : ℝ)..1, f w t) (interior K) := by
    apply hmi.congr
    intro w hw
    rw [extendCompactFunction_apply _ (interior_subset hw)]
    change _ = ContinuousMap.evalCLM ℂ ⟨w, interior_subset hw⟩ (∫ t in (0 : ℝ)..1, g t)
    rw [← (ContinuousMap.evalCLM ℂ ⟨w, interior_subset hw⟩).intervalIntegral_comp_comm hgi]
    apply intervalIntegral.integral_congr
    intro t ht
    change f w t = g t ⟨w, interior_subset hw⟩
    exact (hga t (by simpa only [uIcc_of_le zero_le_one] using ht) ⟨w, interior_subset hw⟩).symm
  apply (hdint.differentiableAt ?_).differentiableWithinAt
  change interior (closedBall z r) ∈ 𝓝 z
  rw [interior_closedBall _ hr.ne']
  exact ball_mem_nhds z hr

theorem dslope_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (a b : ℂ) : dslope f a b = dslope f b a := by
  by_cases he : a = b
  · rw [he]
  · rw [dslope_of_ne _ (Ne.symm he), dslope_of_ne _ he, slope_comm]

theorem continuousAt_dslope_pair_of_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {x : ℂ}
    (hf : AnalyticAt ℂ f x) :
    ContinuousAt (fun p : ℂ × ℂ => dslope f p.1 p.2) (x, x) := by
  change Tendsto _ _ (𝓝 (dslope f x x))
  rw [dslope_same]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hs := hf.hasStrictDerivAt.hasStrictFDerivAt.isLittleO
  have hb := (continuous_swap.tendsto (x, x)).eventually (hs.def (half_pos hε))
  have hd : Tendsto (fun p : ℂ × ℂ => deriv f p.1) (𝓝 (x, x)) (𝓝 (deriv f x)) :=
    hf.deriv.continuousAt.tendsto.comp continuous_fst.continuousAt.tendsto
  filter_upwards [hb, Metric.tendsto_nhds.mp hd ε hε] with p hp hpd
  by_cases he : p.2 = p.1
  · simpa only [he, dslope_same] using hpd
  · have hn : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr he
    have hp' : ‖f p.2 - f p.1 - (p.2 - p.1) • deriv f x‖ ≤
        (ε / 2) * ‖p.2 - p.1‖ := hp
    have heq : dslope f p.1 p.2 - deriv f x =
        (p.2 - p.1)⁻¹ • (f p.2 - f p.1 - (p.2 - p.1) • deriv f x) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul, dslope_of_ne _ he]
      rfl
    rw [dist_eq_norm, heq, norm_smul, norm_inv]
    calc
      _ ≤ ‖p.2 - p.1‖⁻¹ * ((ε / 2) * ‖p.2 - p.1‖) :=
        mul_le_mul_of_nonneg_left hp' (by positivity)
      _ = ε / 2 := by field_simp [norm_ne_zero_iff.mpr hn]
      _ < ε := half_lt_self hε

theorem continuousOn_dslope_pair {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fun p : ℂ × ℂ => dslope f p.1 p.2) (U ×ˢ U) := by
  intro p hp
  by_cases he : p.2 = p.1
  · rcases p with ⟨a, b⟩
    dsimp only at he hp ⊢
    subst b
    exact (continuousAt_dslope_pair_of_analyticAt (hf.analyticOnNhd hU a hp.1)).continuousWithinAt
  · have hc : ContinuousAt (fun p : ℂ × ℂ =>
        (p.2 - p.1)⁻¹ • (f p.2 - f p.1)) p :=
      ((continuous_snd.sub continuous_fst).continuousAt.inv₀ (sub_ne_zero.mpr he)).smul
        (((hf.continuousOn.continuousAt (hU.mem_nhds hp.2)).comp continuous_snd.continuousAt).sub
          ((hf.continuousOn.continuousAt (hU.mem_nhds hp.1)).comp continuous_fst.continuousAt))
    apply (hc.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [(isOpen_ne_fun continuous_snd continuous_fst).mem_nhds he] with q hq
    exact dslope_of_ne f hq

def SmoothContour.integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Γ : SmoothContour) (f : ℂ → E) : E :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    ∫ t in (0 : ℝ)..1, deriv Γ.path t • f (Γ.path t)

def SmoothContour.cauchyTransform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Γ : SmoothContour) (f : ℂ → E) (w : ℂ) : E :=
  Γ.integral (fun z => (z - w)⁻¹ • f z)

def SmoothContour.regularizedTransform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Γ : SmoothContour) (f : ℂ → E) (w : ℂ) : E :=
  Γ.integral (dslope f w)

theorem SmoothContour.intervalIntegrable_contourIntegrand {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (Γ : SmoothContour) {f : ℂ → E}
    (hf : ContinuousOn f Γ.trace) :
    IntervalIntegrable (fun t => deriv Γ.path t • f (Γ.path t)) volume (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  exact Γ.smooth.continuous_deriv_one.continuousOn.smul
    (hf.comp Γ.smooth.continuous.continuousOn (fun t ht => ⟨t, ht, rfl⟩))

theorem SmoothContour.differentiableOn_cauchyTransform {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : SmoothContour) {f : ℂ → E} (hf : ContinuousOn f Γ.trace) :
    DifferentiableOn ℂ (Γ.cauchyTransform f) Γ.traceᶜ := by
  apply DifferentiableOn.const_smul
  apply differentiableOn_parameter_intervalIntegral Γ.isCompact_trace.isClosed.isOpen_compl
  · have hc : Continuous (fun p : ℂ × ℝ => deriv Γ.path p.2) :=
      Γ.smooth.continuous_deriv_one.comp continuous_snd
    apply hc.continuousOn.smul
    apply ContinuousOn.smul
    · apply ContinuousOn.inv₀
      · exact ((Γ.smooth.continuous.comp continuous_snd).sub continuous_fst).continuousOn
      · intro p hp he
        exact hp.1 ⟨p.2, hp.2, sub_eq_zero.mp he⟩
    · exact hf.comp (Γ.smooth.continuous.comp continuous_snd).continuousOn
        (fun p hp => ⟨p.2, hp.2, rfl⟩)
  · intro t ht
    apply DifferentiableOn.const_smul
    apply DifferentiableOn.smul_const
    apply DifferentiableOn.inv
    · exact ((differentiable_const (Γ.path t)).sub differentiable_id).differentiableOn
    · intro w hw he
      exact hw ⟨t, ht, sub_eq_zero.mp he⟩

theorem SmoothContour.differentiableOn_regularizedTransform {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : SmoothContour) {U : Set ℂ} (hU : IsOpen U) (hΓ : Γ.trace ⊆ U)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (Γ.regularizedTransform f) U := by
  apply DifferentiableOn.const_smul
  apply differentiableOn_parameter_intervalIntegral hU
  · apply (Γ.smooth.continuous_deriv_one.comp continuous_snd).continuousOn.smul
    apply (continuousOn_dslope_pair hU hf).comp
      (continuous_fst.prodMk (Γ.smooth.continuous.comp continuous_snd)).continuousOn
    intro p hp
    exact ⟨hp.1, hΓ ⟨p.2, hp.2, rfl⟩⟩
  · intro t ht
    apply DifferentiableOn.const_smul
    have hd := (Complex.differentiableOn_dslope (hU.mem_nhds (hΓ ⟨t, ht, rfl⟩))).mpr hf
    exact hd.congr (fun w _ => dslope_swap f w (Γ.path t))

theorem SmoothContour.regularizedTransform_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : SmoothContour) {f : ℂ → E} (hf : ContinuousOn f Γ.trace)
    {w : ℂ} (hw : w ∉ Γ.trace) :
    Γ.regularizedTransform f w = Γ.cauchyTransform f w - Γ.index w • f w := by
  have hc : ContinuousOn (fun z : ℂ => (z - w)⁻¹) Γ.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀
      (fun z hz he => hw ((show z = w from sub_eq_zero.mp he) ▸ hz))
  have hi : IntervalIntegrable (fun t => deriv Γ.path t • ((Γ.path t - w)⁻¹ • f (Γ.path t)))
      volume (0 : ℝ) 1 := by
    simpa only [Pi.smul_apply'] using Γ.intervalIntegrable_contourIntegrand (hc.smul hf)
  have hj := (Γ.intervalIntegrable_indexIntegrand hw).smul_continuousOn
    (continuousOn_const (c := f w))
  unfold SmoothContour.regularizedTransform SmoothContour.cauchyTransform SmoothContour.integral
  have he : (∫ t in (0 : ℝ)..1, deriv Γ.path t • dslope f w (Γ.path t)) =
      (∫ t in (0 : ℝ)..1, deriv Γ.path t • ((Γ.path t - w)⁻¹ • f (Γ.path t))) -
      (∫ t in (0 : ℝ)..1, deriv Γ.path t / (Γ.path t - w)) • f w := by
    rw [← intervalIntegral.integral_smul_const, ← intervalIntegral.integral_sub hi hj]
    apply intervalIntegral.integral_congr
    intro t ht
    have hn : Γ.path t ≠ w := fun he => hw ⟨t, by simpa only [uIcc_of_le zero_le_one] using ht, he⟩
    simp only [dslope_of_ne f hn, slope, vsub_eq_sub, smul_sub, smul_smul, div_eq_mul_inv]
  rw [he, smul_sub, smul_smul]
  rfl

theorem SmoothContour.eventually_index_eq (Γ : SmoothContour) {w : ℂ}
    (hw : w ∉ Γ.trace) : ∀ᶠ z in 𝓝 w, Γ.index z = Γ.index w := by
  obtain ⟨r, hr, hrc⟩ := Metric.mem_nhds_iff.mp
    (Γ.isCompact_trace.isClosed.isOpen_compl.mem_nhds hw)
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  apply Γ.index_eq_of_segment_avoids
  intro t ht he
  exact hrc ((convex_ball w r).segment_subset hz (mem_ball_self hr) he) ⟨t, ht, rfl⟩

theorem SmoothContour.tendsto_cauchyTransform_cocompact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : SmoothContour) {f : ℂ → E} (hf : ContinuousOn f Γ.trace) :
    Tendsto (Γ.cauchyTransform f) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨R, hR⟩ := Γ.isCompact_trace.exists_bound_of_continuousOn continuousOn_id
  have hc : ContinuousOn (fun t => deriv Γ.path t • f (Γ.path t)) (Icc (0 : ℝ) 1) :=
    Γ.smooth.continuous_deriv_one.continuousOn.smul
      (hf.comp Γ.smooth.continuous.continuousOn (fun t ht => ⟨t, ht, rfl⟩))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have htop : Tendsto (fun w : ℂ => ‖w‖ - R) (cocompact ℂ) atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right (cocompact ℂ) (-R) tendsto_norm_cocompact_atTop
  have hb : ∀ᶠ w : ℂ in cocompact ℂ,
      ‖∫ t in (0 : ℝ)..1, deriv Γ.path t • ((Γ.path t - w)⁻¹ • f (Γ.path t))‖ ≤
      (‖w‖ - R)⁻¹ * M := by
    filter_upwards [htop.eventually_gt_atTop 0] with w hw
    have hi := @intervalIntegral.norm_integral_le_of_norm_le_const E _ _
      0 1 ((‖w‖ - R)⁻¹ * M)
      (fun t => deriv Γ.path t • ((Γ.path t - w)⁻¹ • f (Γ.path t)))
    simpa only [sub_zero, abs_one, mul_one] using hi (by
      intro t ht
      have htt : t ∈ Icc (0 : ℝ) 1 :=
        Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using ht)
      have hn : ‖w‖ - R ≤ ‖Γ.path t - w‖ := by
        have hne := norm_sub_norm_le w (Γ.path t)
        rw [norm_sub_rev] at hne
        have hr : ‖Γ.path t‖ ≤ R := hR _ ⟨t, htt, rfl⟩
        linarith
      have he : ‖deriv Γ.path t • ((Γ.path t - w)⁻¹ • f (Γ.path t))‖ =
          ‖Γ.path t - w‖⁻¹ * ‖deriv Γ.path t • f (Γ.path t)‖ := by
        simp only [norm_smul, norm_inv]
        ring
      rw [he]
      exact mul_le_mul (inv_anti₀ hw hn) (hM t htt) (norm_nonneg _) (by positivity))
  have hl : Tendsto (fun w : ℂ => (‖w‖ - R)⁻¹ * M) (cocompact ℂ) (𝓝 0) := by
    simpa only [Pi.inv_apply, zero_mul] using htop.inv_tendsto_atTop.mul_const M
  have hi := squeeze_zero_norm' hb hl
  change Tendsto (fun w : ℂ => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    ∫ t in (0 : ℝ)..1, deriv Γ.path t • ((Γ.path t - w)⁻¹ • f (Γ.path t)))
      (cocompact ℂ) (𝓝 0)
  simpa only [smul_zero] using hi.const_smul (2 * (Real.pi : ℂ) * Complex.I)⁻¹

theorem SmoothContour.eventually_index_zero_cocompact (Γ : SmoothContour) :
    ∀ᶠ w : ℂ in cocompact ℂ, w ∉ Γ.trace ∧ Γ.index w = 0 := by
  obtain ⟨R, hR⟩ := Γ.isCompact_trace.exists_bound_of_continuousOn continuousOn_id
  have hsub : Γ.trace ⊆ closedBall (0 : ℂ) R := by
    intro z hz
    simpa only [mem_closedBall, dist_zero_right, id_eq] using hR z hz
  filter_upwards [(isCompact_closedBall (0 : ℂ) R).compl_mem_cocompact] with w hw
  exact ⟨fun h => hw (hsub h), Γ.index_eq_zero_of_convex (convex_closedBall 0 R)
    isClosed_closedBall hsub hw⟩

theorem SmoothContour.tendsto_regularizedTransform_cocompact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : SmoothContour) {f : ℂ → E} (hf : ContinuousOn f Γ.trace) :
    Tendsto (Γ.regularizedTransform f) (cocompact ℂ) (𝓝 0) := by
  apply (Γ.tendsto_cauchyTransform_cocompact hf).congr'
  filter_upwards [Γ.eventually_index_zero_cocompact] with w hw
  rw [Γ.regularizedTransform_eq hf hw.1, hw.2, zero_smul, sub_zero]

theorem sum_regularizedTransform_eq_zero {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : ι → SmoothContour) (c : ι → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hΓ : ∀ i, (Γ i).trace ⊆ U)
    (hnull : ∀ w ∉ U, ∑ i, c i * (Γ i).index w = 0)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) (w : ℂ) :
    ∑ i, c i • (Γ i).regularizedTransform f w = 0 := by
  let g : ℂ → E := fun z => ∑ i, c i • (Γ i).regularizedTransform f z
  have hfc (i : ι) : ContinuousOn f (Γ i).trace := hf.continuousOn.mono (hΓ i)
  have heq (v : ℂ) (hv : ∀ i, v ∉ (Γ i).trace) : g v =
      (∑ i, c i • (Γ i).cauchyTransform f v) - (∑ i, c i * (Γ i).index v) • f v := by
    dsimp only [g]
    simp_rw [(Γ _).regularizedTransform_eq (hfc _) (hv _), smul_sub, smul_smul]
    rw [Finset.sum_sub_distrib, Finset.sum_smul]
  have hd : Differentiable ℂ g := by
    intro v
    by_cases hv : v ∈ U
    · apply DifferentiableAt.fun_sum
      intro i _
      exact ((Γ i).differentiableOn_regularizedTransform hU (hΓ i) hf
        |>.differentiableAt (hU.mem_nhds hv)).const_smul (c i)
    · have hvΓ (i : ι) : v ∉ (Γ i).trace := fun hi => hv (hΓ i hi)
      have hc : DifferentiableAt ℂ (fun z => ∑ i, c i • (Γ i).cauchyTransform f z) v := by
        apply DifferentiableAt.fun_sum
        intro i _
        exact ((Γ i).differentiableOn_cauchyTransform (hfc i)
          |>.differentiableAt ((Γ i).isCompact_trace.isClosed.isOpen_compl.mem_nhds (hvΓ i))).const_smul (c i)
      apply hc.congr_of_eventuallyEq
      have hi (i : ι) : ∀ᶠ z in 𝓝 v, z ∉ (Γ i).trace ∧ (Γ i).index z = (Γ i).index v :=
        (show ∀ᶠ z in 𝓝 v, z ∉ (Γ i).trace from
          (Γ i).isCompact_trace.isClosed.isOpen_compl.mem_nhds (hvΓ i)).and
          ((Γ i).eventually_index_eq (hvΓ i))
      filter_upwards [eventually_all.mpr hi] with z hz
      rw [heq z (fun i => (hz i).1)]
      have he : (∑ i, c i * (Γ i).index z) = 0 := by
        simpa only [(hz _).2] using hnull v hv
      rw [he, zero_smul, sub_zero]
  have ht : Tendsto g (cocompact ℂ) (𝓝 0) := by
    have hti (i : ι) := ((Γ i).tendsto_regularizedTransform_cocompact (hfc i)).const_smul (c i)
    simpa only [g, smul_zero, Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hti i)
  exact hd.apply_eq_of_tendsto_cocompact w ht

theorem sum_integral_eq_zero_of_null_homology {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : ι → SmoothContour) (c : ι → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hΓ : ∀ i, (Γ i).trace ⊆ U)
    (hnull : ∀ w ∉ U, ∑ i, c i * (Γ i).index w = 0)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) :
    ∑ i, c i • (Γ i).integral f = 0 := by
  have he := sum_regularizedTransform_eq_zero Γ c hU hΓ hnull
    (differentiableOn_id.fun_smul hf) 0
  convert! he using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold SmoothContour.regularizedTransform SmoothContour.integral
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change deriv (Γ i).path t • f ((Γ i).path t) =
    deriv (Γ i).path t • dslope (fun z => z • f z) 0 ((Γ i).path t)
  congr 1
  have htU : (Γ i).path t ∈ U := hΓ i ⟨t, by simpa only [uIcc_of_le zero_le_one] using ht, rfl⟩
  by_cases hz : (Γ i).path t = 0
  · rw [hz, dslope_same]
    have hd := (hasDerivAt_id (0 : ℂ)).fun_smul
      ((hf.differentiableAt (hU.mem_nhds (hz ▸ htU))).hasDerivAt)
    simpa only [id_eq, one_smul, zero_smul, zero_add] using hd.deriv.symm
  · rw [dslope_of_ne _ hz]
    simp only [slope, vsub_eq_sub, sub_zero, zero_smul, inv_smul_smul₀ hz]

end CrouzeixHilbert

end

end OAI
