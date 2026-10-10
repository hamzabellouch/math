import Mathlib
import OAI.Analysis.MumfordShah.HarmonicAnalysis
import OAI.Analysis.MumfordShah.HarmonicProjection

namespace OAI

/-! MumfordShah exterior potential. -/

noncomputable section
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
namespace MumfordShah
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter
open scoped ContDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Filter
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set Metric Topology InnerProductSpace Complex MeasureTheory
open scoped ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff

lemma sq_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ) * (∫ x, (g x)^2 ∂μ) := by
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  have hi {a b : α → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
      inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x * b x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx hy
    simp [hx, hy, mul_comm]
  rw [hi hf hg, hi hf hf, hi hg hg] at h
  simpa only [pow_two] using h

lemma radialBump_integral_scale (r : ℝ) :
    (∫ z, radialBump r z) = r^2 * (∫ z, radialBump 1 z) := by
  have h := Measure.integral_comp_inv_smul volume (radialBump 1) r
  simpa [radialBump, Complex.finrank_real_complex, abs_of_nonneg (sq_nonneg r), smul_eq_mul] using h

lemma radialBump_sq_integral_scale (r : ℝ) :
    (∫ z, (radialBump r z)^2) = r^2 * (∫ z, (radialBump 1 z)^2) := by
  have h := Measure.integral_comp_inv_smul volume (fun z => (radialBump 1 z)^2) r
  simpa [radialBump, Complex.finrank_real_complex, abs_of_nonneg (sq_nonneg r), smul_eq_mul] using h

lemma continuous_extension_closedBall {f : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hf : ContinuousOn f (closedBall c R)) :
    ∃ g : ℂ → ℝ, Continuous g ∧ EqOn g f (closedBall c R) := by
  let F : C(closedBall c R, ℝ) := ⟨fun x => f x, hf.domRestrict⟩
  obtain ⟨G,hG⟩ := F.exists_restrict_eq isClosed_closedBall
  refine ⟨G, G.continuous, fun x hx => ?_⟩
  exact congrArg (fun h : C(closedBall c R, ℝ) => h ⟨x,hx⟩) hG

lemma radialBump_local_mean {f : ℂ → ℝ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : HarmonicOnNhd f (ball c (3*r))) :
    (∫ z in ball 0 (2*r), radialBump r z * f (c+z)) =
      (∫ z, radialBump r z) * f c := by
  let R : ℝ := 5*r/2
  have hR : 2*r < R ∧ R < 3*r := by dsimp [R]; constructor <;> linarith
  have hfc : ContinuousOn f (closedBall c R) :=
    (hf.mono (closedBall_subset_ball hR.2)).continuousOn
  obtain ⟨g,hg,hgf⟩ := continuous_extension_closedBall hfc
  have he (x : ℂ) (hx : x ∈ closedBall c (2*r)) : f =ᶠ[𝓝 x] g := by
    have hxR : x ∈ ball c R := closedBall_subset_ball hR.1 hx
    filter_upwards [isOpen_ball.mem_nhds hxR] with y hy
    exact (hgf (ball_subset_closedBall hy)).symm
  have hgh : HarmonicOnNhd g (closedBall c (2*r)) := by
    intro x hx
    apply (harmonicAt_congr_nhds (he x hx)).mp
    exact hf x (closedBall_subset_ball (by linarith) hx)
  have hm := radial_weighted_harmonic_mean (radialBump_contDiff r).continuous hg
    (by rw [radialBump_support hr]; exact ball_subset_closedBall)
    (radialBump_radial r) hgh
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball 0 (2*r))
    (fun z hz => by rw [show radialBump r z = 0 from Function.notMem_support.mp (by rwa [radialBump_support hr])]; simp)] at hm
  have hcR : c ∈ closedBall c R := mem_closedBall_self (by dsimp [R]; positivity)
  rw [hgf hcR] at hm
  rw [← hm]
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  change radialBump r z * f (c+z) = radialBump r z * g (c+z)
  congr 1
  apply (hgf _).symm
  apply ball_subset_closedBall
  have : dist (c+z) c = ‖z‖ := by simp [dist_eq_norm]
  rw [mem_ball, this]
  calc ‖z‖ < 2*r := by simpa using hz
       _ < R := hR.1

lemma harmonic_l2_point_bound {f : ℂ → ℝ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : HarmonicOnNhd f (ball c (3*r))) :
    r^2 * f c ^ 2 ≤
      ((∫ z : ℂ, (radialBump 1 z)^2) / (∫ z : ℂ, radialBump 1 z)^2) *
        ∫ z in ball 0 (2*r), f (c+z)^2 := by
  let μ := volume.restrict (ball (0 : ℂ) (2*r))
  have hc : IsCompact (closedBall (0 : ℂ) (2*r)) := isCompact_closedBall _ _
  have hfc : ContinuousOn (fun z => f (c+z)) (closedBall 0 (2*r)) := by
    apply (hf.continuousOn).comp (by fun_prop)
    intro z hz
    have : dist (c+z) c = ‖z‖ := by simp [dist_eq_norm]
    rw [mem_ball, this]
    have : ‖z‖ ≤ 2*r := by simpa using hz
    linarith
  have hfl : MemLp (fun z => f (c+z)) 2 μ :=
    ((memLp_two_iff_integrable_sq (hfc.aestronglyMeasurable hc.measurableSet)).mpr
      ((hfc.pow 2).integrableOn_compact hc)).mono_measure (Measure.restrict_mono ball_subset_closedBall le_rfl)
  have hkl : MemLp (radialBump r) 2 μ :=
    ((radialBump_contDiff r).continuous.memLp_of_hasCompactSupport (radialBump_compact hr) (p := 2)).restrict _
  have hCS := sq_integral_mul_le hkl hfl
  change (∫ z in ball 0 (2*r), radialBump r z * f (c+z))^2 ≤
    (∫ z in ball 0 (2*r), (radialBump r z)^2) *
    (∫ z in ball 0 (2*r), f (c+z)^2) at hCS
  rw [radialBump_local_mean hr hf] at hCS
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
    rw [show radialBump r z = 0 from Function.notMem_support.mp (by rwa [radialBump_support hr])]; simp),
    radialBump_integral_scale, radialBump_sq_integral_scale] at hCS
  have hJ : 0 < ∫ z : ℂ, radialBump 1 z := radialBump_integral_pos zero_lt_one
  rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hJ)]
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hr)).mp
  convert hCS using 1 <;> first | rfl | ring

lemma integral_square_tail_tendsto_zero {f : ℂ → ℝ}
    (hf : Integrable (fun z => (f z)^2)) :
    Tendsto (fun R : ℝ => ∫ z in {z : ℂ | R ≤ ‖z‖}, (f z)^2) atTop (𝓝 0) := by
  have he : (⋂ R : ℝ, {z : ℂ | R ≤ ‖z‖}) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have := mem_iInter.mp hz (‖z‖+1)
    simp only [mem_ofPred_eq] at this
    linarith
  have ht := tendsto_setIntegral_of_antitone
    (f := fun z : ℂ => (f z)^2) (μ := volume)
    (s := fun R : ℝ => {z : ℂ | R ≤ ‖z‖})
    (fun R => isClosed_le continuous_const continuous_norm |>.measurableSet)
    (fun R S h z hz => le_trans h hz) ⟨0, hf.integrableOn⟩
  simpa [he] using ht

lemma integral_ball_translate (F : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    (∫ z in ball (0 : ℂ) r, F (c+z)) = ∫ z in ball c r, F z := by
  have hpre : (fun z : ℂ => c+z) ⁻¹' ball c r = ball 0 r := by
    ext z
    simp [mem_ball, dist_eq_norm]
  rw [← hpre]
  exact (measurePreserving_add_left volume c).setIntegral_preimage_emb
    (Homeomorph.addLeft c).measurableEmbedding F _

lemma harmonic_l2_exterior_little_o {f : ℂ → ℝ} {R : ℝ}
    (hf : HarmonicOnNhd f {z | R < ‖z‖})
    (hL : Integrable (fun z => (f z)^2)) :
    Tendsto (fun z : ℂ => ‖z‖ * f z) (cocompact ℂ) (𝓝 0) := by
  let C : ℝ := (∫ z : ℂ, (radialBump 1 z)^2) / (∫ z : ℂ, radialBump 1 z)^2
  have hC : 0 ≤ C := div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (sq_nonneg _)
  let tail : ℝ → ℝ := fun r => ∫ z in {z : ℂ | r ≤ ‖z‖}, (f z)^2
  have ht : Tendsto tail atTop (𝓝 0) := integral_square_tail_tendsto_zero hL
  have hb : ∀ᶠ c : ℂ in cocompact ℂ,
      (‖c‖ * f c)^2 ≤ 64*C*tail (‖c‖/2) := by
    filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop (max 0 (2*R)))] with c hc
    have hcn : 0 < ‖c‖ := lt_of_le_of_lt (le_max_left _ _) hc
    have hcR : 2*R < ‖c‖ := lt_of_le_of_lt (le_max_right _ _) hc
    have hcb : ball c (3*(‖c‖/8)) ⊆ {z | R < ‖z‖} := by
      intro z hz
      have hdist : ‖c‖ ≤ ‖z-c‖ + ‖z‖ := by
        calc ‖c‖ = ‖(c-z)+z‖ := by congr 1; ring
             _ ≤ ‖c-z‖+‖z‖ := norm_add_le _ _
             _ = ‖z-c‖+‖z‖ := by rw [norm_sub_rev]
      have hz' : ‖z-c‖ < 3*(‖c‖/8) := by simpa [mem_ball, dist_eq_norm] using hz
      change R < ‖z‖
      linarith
    have he := harmonic_l2_point_bound (by positivity : 0 < ‖c‖/8) (hf.mono hcb)
    rw [integral_ball_translate (fun z => (f z)^2) c] at he
    change (‖c‖/8)^2 * f c ^ 2 ≤ C * ∫ z in ball c (2*(‖c‖/8)), (f z)^2 at he
    have hsub : ball c (2*(‖c‖/8)) ⊆ {z : ℂ | ‖c‖/2 ≤ ‖z‖} := by
      intro z hz
      have hdist : ‖c‖ ≤ ‖z-c‖ + ‖z‖ := by
        calc ‖c‖ = ‖(c-z)+z‖ := by congr 1; ring
             _ ≤ ‖c-z‖+‖z‖ := norm_add_le _ _
             _ = ‖z-c‖+‖z‖ := by rw [norm_sub_rev]
      have hz' : ‖z-c‖ < 2*(‖c‖/8) := by simpa [mem_ball, dist_eq_norm] using hz
      change ‖c‖/2 ≤ ‖z‖
      linarith
    have hi : (∫ z in ball c (2*(‖c‖/8)), (f z)^2) ≤ tail (‖c‖/2) := by
      apply setIntegral_mono_set hL.integrableOn
      · exact ae_of_all _ (fun z => sq_nonneg (f z))
      · exact ae_of_all _ hsub
    have := he.trans (mul_le_mul_of_nonneg_left hi hC)
    nlinarith
  have hd : Tendsto (fun z : ℂ => ‖z‖/2) (cocompact ℂ) atTop :=
    tendsto_norm_cocompact_atTop.atTop_div_const (by norm_num)
  have hs : Tendsto (fun z : ℂ => (‖z‖ * f z)^2) (cocompact ℂ) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) hb
      (by simpa using (ht.comp hd).const_mul (64*C))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa [Function.comp_def, Real.sqrt_sq_eq_abs, Real.norm_eq_abs] using hh

lemma holomorphic_l2_exterior_little_o {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g {z | R < ‖z‖}) (hL : MemLp g 2 volume) :
    Tendsto (fun z : ℂ => ‖z‖ * ‖g z‖) (cocompact ℂ) (𝓝 0) := by
  have htr := harmonic_l2_exterior_little_o (f := fun z => (g z).re)
    (fun z hz => (hg z hz).harmonicAt_re) (Complex.reCLM.comp_memLp' hL).integrable_sq
  have hti := harmonic_l2_exterior_little_o (f := fun z => (g z).im)
    (fun z hz => (hg z hz).harmonicAt_im) (Complex.imCLM.comp_memLp' hL).integrable_sq
  have ht := htr.ofReal.add (hti.ofReal.mul_const Complex.I)
  have hc : Tendsto (fun z : ℂ => (‖z‖ : ℂ) * g z) (cocompact ℂ) (𝓝 0) := by
    convert ht using 1
    · ext z
      apply Complex.ext <;> simp
    · simp
  simpa [norm_mul] using hc.norm

lemma exterior_holomorphic_double_zero {g : ℂ → ℂ} {R : ℝ}
    (hg : ∀ z, R < ‖z‖ → DifferentiableAt ℂ g z)
    (ht : Tendsto (fun z => ‖z‖ * ‖g z‖) (cocompact ℂ) (𝓝 0)) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ᶠ w in 𝓝[≠] (0 : ℂ), g w⁻¹ = w^2 * H w := by
  let G : ℂ → ℂ := fun w => if w = 0 then 0 else g w⁻¹
  have hG0 : G 0 = 0 := by simp [G]
  have hi : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
    simpa [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_nhdsNE_zero (α := ℂ))
  have hGs : HasDerivAt G 0 0 := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply (ht.comp hi).congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw0 : w ≠ 0 := hw
    simp [slope, hG0, G, hw0, norm_inv]
  have hGa : AnalyticAt ℂ G 0 := by
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (hc := hGs.continuousAt)
    filter_upwards [tendsto_norm_inv_nhdsNE_zero_atTop.eventually (eventually_gt_atTop R),
      self_mem_nhdsWithin] with w hw hw0
    have hw0' : w ≠ 0 := hw0
    have hd : DifferentiableAt ℂ (fun v : ℂ => g v⁻¹) w :=
      (hg _ hw).comp w (differentiableAt_inv hw0')
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hw0'] with v hv
    simp [G, hv]
  obtain ⟨H, hHa, hH⟩ := hGa.exists_eventuallyEq_sum_add_pow_mul 2
  refine ⟨H, hHa, ?_⟩
  filter_upwards [hH.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hw0
  have hw0' : w ≠ 0 := hw0
  simpa [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
    hGs.deriv, hG0, G, hw0', smul_eq_mul] using hw

lemma fderiv_eq_re_complexPartial (u : ℂ → ℝ) (z a : ℂ) :
    fderiv ℝ u z a = (complexPartial u z * a).re := by
  have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by
    simp
  conv_lhs => rw [ha, map_add, map_smul, map_smul]
  simp [complexPartial, Complex.mul_re, Complex.mul_im]
  ring

lemma real_fderiv_of_hasDerivAt {F : ℂ → ℂ} {d w : ℂ}
    (hF : HasDerivAt F d w) (a : ℂ) : fderiv ℝ F w a = d*a := by
  rw [(hF.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp [mul_comm]

lemma punctured_ball_preconnected {r : ℝ} (hr : 0 < r) :
    IsPreconnected (ball (0 : ℂ) r \ {0}) := by
  have himg : Complex.exp '' {z : ℂ | z.re < Real.log r} = ball 0 r \ {0} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, by simp⟩
      simp only [mem_ball, dist_zero_right, Complex.norm_exp]
      exact (Real.lt_log_iff_exp_lt hr).mp hz
    · intro hw
      have hw0 : w ≠ 0 := by simpa using hw.2
      refine ⟨Complex.log w, ?_, Complex.exp_log hw0⟩
      change (Complex.log w).re < Real.log r
      rw [Complex.log_re]
      exact Real.strictMonoOn_log (by simpa using hw0) hr (by simpa using hw.1)
  rw [← himg]
  exact (convex_halfSpace_re_lt (Real.log r)).isPreconnected.image
    Complex.exp Complex.continuous_exp.continuousOn

lemma harmonic_inversion_analytic_representation {u : ℂ → ℝ} {R : ℝ} {H : ℂ → ℂ}
    (hu : HarmonicOnNhd u {z | R < ‖z‖}) (hH : AnalyticAt ℂ H 0)
    (he : ∀ᶠ w in 𝓝[≠] (0 : ℂ), complexPartial u w⁻¹ = w^2 * H w) :
    ∃ F : ℂ → ℂ, ∃ c : ℝ, AnalyticAt ℂ F 0 ∧
      ∀ᶠ z : ℂ in cocompact ℂ, u z = (F z⁻¹).re + c := by
  have hex : ∀ᶠ w : ℂ in 𝓝[≠] 0, R < ‖w⁻¹‖ :=
    tendsto_norm_inv_nhdsNE_zero_atTop.eventually (eventually_gt_atTop R)
  have hd := hH.eventually_analyticAt.and
    (eventually_nhdsWithin_iff.mp (hex.and he))
  obtain ⟨r, hr, hrd⟩ := Metric.eventually_nhds_iff.mp hd
  have hHa : AnalyticOnNhd ℂ H (ball 0 r) := fun w hw => (hrd (by simpa using hw)).1
  have hHd : DifferentiableOn ℂ (fun w => -H w) (ball 0 r) := hHa.differentiableOn.neg
  obtain ⟨F, hFd⟩ := hHd.isExactOn_ball
  have hFa : AnalyticOnNhd ℂ F (ball 0 r) :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (hFd w hw).differentiableAt.differentiableWithinAt) isOpen_ball
  let S : Set ℂ := ball 0 r \ {0}
  have hS : IsOpen S := isOpen_ball.sdiff isClosed_singleton
  have hSp : IsPreconnected S := punctured_ball_preconnected hr
  have hudi (w : ℂ) (hw : w ∈ S) : DifferentiableAt ℝ u w⁻¹ :=
    (hu _ ((hrd (by simpa using hw.1)).2 (by simpa using hw.2)).1).1.differentiableAt (by norm_num)
  have hud : DifferentiableOn ℝ (fun w : ℂ => u w⁻¹) S := by
    intro w hw
    exact ((hudi w hw).comp w
      ((differentiableAt_inv (𝕜 := ℂ) (by simpa using hw.2)).restrictScalars ℝ)).differentiableWithinAt
  have hfr : DifferentiableOn ℝ (fun w : ℂ => (F w).re) S := by
    intro w hw
    exact (Complex.reCLM.differentiableAt.comp w
      ((hFd w hw.1).differentiableAt.restrictScalars ℝ)).differentiableWithinAt
  have heq : S.EqOn (fderiv ℝ (fun w : ℂ => u w⁻¹))
      (fderiv ℝ (fun w : ℂ => (F w).re)) := by
    intro w hw
    have hw0 : w ≠ 0 := by simpa using hw.2
    have hcp := ((hrd (by simpa using hw.1)).2 hw0).2
    ext a
    change (fderiv ℝ (u ∘ Inv.inv) w) a = (fderiv ℝ (Complex.reCLM ∘ F) w) a
    rw [fderiv_comp w (hudi w hw) ((differentiableAt_inv (𝕜 := ℂ) hw0).restrictScalars ℝ)]
    rw [fderiv_comp w Complex.reCLM.differentiableAt
      ((hFd w hw.1).differentiableAt.restrictScalars ℝ)]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv,
      Complex.reCLM_apply]
    rw [real_fderiv_of_hasDerivAt (hasDerivAt_inv hw0),
      fderiv_eq_re_complexPartial, hcp, real_fderiv_of_hasDerivAt (hFd w hw.1)]
    congr 1
    field_simp
  obtain ⟨c, hc⟩ := hS.exists_eq_add_of_fderiv_eq hSp hud hfr heq
  refine ⟨F, c, hFa 0 (mem_ball_self hr), ?_⟩
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝[≠] 0) := by
    simpa [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded' (α := ℂ))
  have hn : S ∈ 𝓝[≠] (0 : ℂ) := by
    simpa [S, sdiff_eq_compl_inter] using inter_mem_nhdsWithin ({0}ᶜ : Set ℂ) (ball_mem_nhds (0 : ℂ) hr)
  filter_upwards [hi.eventually hn] with z hz
  simpa using hc hz

lemma complexPartial_eq_conj_gradient (u : ℂ → ℝ) (z : ℂ) :
    complexPartial u z = star (gradient u z) := by
  have hi (a : ℂ) : inner ℝ (gradient u z) a =
      (gradient u z).re * a.re + (gradient u z).im * a.im := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
    change (a * star (gradient u z)).re = _
    simp [Complex.mul_re]
    ring
  unfold complexPartial
  rw [← inner_gradient_left, ← inner_gradient_left, hi, hi]
  apply Complex.ext <;> simp

theorem finite_energy_harmonic_exterior_representation
    {u : ℂ → ℝ} {w : ℂ → ℂ} {R : ℝ}
    (hu : HarmonicOnNhd u {z | R < ‖z‖}) (hw : MemLp w 2 volume)
    (he : ∀ᵐ z ∂volume, R < ‖z‖ → gradient u z = w z) :
    ∃ A : ℂ → ℂ, ∃ c : ℝ, AnalyticAt ℂ A 0 ∧
      ∀ᶠ z : ℂ in cocompact ℂ, u z - c = (z⁻¹ * A z⁻¹).re := by
  let O : Set ℂ := {z | R < ‖z‖}
  have hO : IsOpen O := isOpen_lt continuous_const continuous_norm
  let g : ℂ → ℂ := O.indicator (complexPartial u)
  have hga : AnalyticOnNhd ℂ g O := by
    intro z hz
    apply (_root_.HarmonicAt.analyticAt_complex_partial (hu z hz)).congr
    filter_upwards [hO.mem_nhds hz] with y hy
    simp [g, hy, complexPartial]
  have hgL : MemLp g 2 volume := by
    apply MemLp.ae_eq (hf_Lp := (Complex.conjCLE.toContinuousLinearMap.comp_memLp' hw).indicator hO.measurableSet)
    filter_upwards [he] with z hz
    by_cases ho : z ∈ O
    · simp [g, ho, complexPartial_eq_conj_gradient, hz ho]
    · simp [g, ho]
  obtain ⟨H, hH, hh⟩ := exterior_holomorphic_double_zero
    (fun z hz => (hga z hz).differentiableAt) (holomorphic_l2_exterior_little_o hga hgL)
  have hh' : ∀ᶠ v in 𝓝[≠] (0 : ℂ), complexPartial u v⁻¹ = v^2 * H v := by
    filter_upwards [hh, tendsto_norm_inv_nhdsNE_zero_atTop.eventually (eventually_gt_atTop R)] with v hv hvR
    simpa [g, show v⁻¹ ∈ O from hvR] using hv
  obtain ⟨F, c, hF, hf⟩ := harmonic_inversion_analytic_representation hu hH hh'
  obtain ⟨A, hA, hrep⟩ := hF.exists_eventuallyEq_sum_add_pow_mul 1
  refine ⟨A, c + (F 0).re, hA, ?_⟩
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  filter_upwards [hf, hi.eventually hrep] with z hz hez
  simp only [Finset.sum_range_one, iteratedDeriv_zero, Nat.factorial_zero,
    Nat.cast_one, pow_zero, pow_one] at hez
  rw [hz, hez]
  simp only [one_div_one, smul_eq_mul, Complex.add_re]
  ring_nf

lemma eventually_nhds_of_cocompact {P : ℂ → Prop}
    (h : ∀ᶠ z in cocompact ℂ, P z) :
    ∀ᶠ z in cocompact ℂ, ∀ᶠ w in 𝓝 z, P w := by
  obtain ⟨K, hK, hKP⟩ := Filter.hasBasis_cocompact.eventually_iff.mp h
  filter_upwards [hK.compl_mem_cocompact] with z hz
  filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with w hw
  exact hKP hw

lemma inverted_analytic_iteratedDeriv {A : ℂ → ℂ} (hA : AnalyticAt ℂ A 0) (n : ℕ) :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧
      ∀ᶠ z in cocompact ℂ,
        iteratedDeriv n (fun z : ℂ => z⁻¹ * A z⁻¹) z = z⁻¹ ^ (n+1) * B z⁻¹ := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hne : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 :=
    isCompact_singleton.compl_mem_cocompact
  induction n with
  | zero => exact ⟨A, hA, by simp⟩
  | succ n ih =>
    obtain ⟨B, hB, hBe⟩ := ih
    let C : ℂ → ℂ := fun w => -((n+1 : ℂ)*B w + w*deriv B w)
    have hC : AnalyticAt ℂ C 0 :=
      ((analyticAt_const.mul hB).add (analyticAt_id.mul hB.deriv)).neg
    refine ⟨C, hC, ?_⟩
    filter_upwards [eventually_nhds_of_cocompact hBe, hne,
      hi.eventually hB.eventually_analyticAt] with z he hz hb
    rw [iteratedDeriv_succ, Filter.EventuallyEq.deriv_eq he]
    have hd := ((hasDerivAt_inv hz).pow (n+1)).mul
      (hb.differentiableAt.hasDerivAt.comp z (hasDerivAt_inv hz))
    change deriv (((fun y : ℂ => y⁻¹) ^ (n+1)) * (B ∘ Inv.inv)) z = _
    rw [hd.deriv]
    dsimp [C]
    simp only [inv_pow, pow_succ]
    push_cast
    ring

lemma inverted_analytic_derivative_decay {A : ℂ → ℂ} (hA : AnalyticAt ℂ A 0) (n : ℕ) :
    ∃ C : ℝ, ∀ᶠ z in cocompact ℂ,
      ‖iteratedDeriv n (fun z : ℂ => z⁻¹ * A z⁻¹) z‖ ≤ C * ‖z‖⁻¹ ^ (n+1) := by
  obtain ⟨B, hB, he⟩ := inverted_analytic_iteratedDeriv hA n
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hb : ∀ᶠ w in 𝓝 (0 : ℂ), ‖B w‖ ≤ ‖B 0‖ + 1 := by
    filter_upwards [hB.continuousAt.norm.eventually (gt_mem_nhds (by linarith : ‖B 0‖ < ‖B 0‖+1))] with w hw
    exact hw.le
  refine ⟨‖B 0‖+1, ?_⟩
  filter_upwards [he, hi.eventually hb] with z hz hbz
  rw [hz, norm_mul, norm_pow, norm_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right hbz (by positivity)

lemma real_part_inverse_derivative_decay {A : ℂ → ℂ} (hA : AnalyticAt ℂ A 0) (n : ℕ) :
    ∃ C : ℝ, ∀ᶠ z in cocompact ℂ,
      ‖iteratedFDeriv ℝ n (fun z : ℂ => (z⁻¹ * A z⁻¹).re) z‖ ≤
        C * ‖z‖⁻¹ ^ (n+1) := by
  obtain ⟨C, hC⟩ := inverted_analytic_derivative_decay hA n
  refine ⟨‖Complex.reCLM‖ * C, ?_⟩
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  filter_upwards [hC, hi.eventually hA.eventually_analyticAt,
    (show ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 from isCompact_singleton.compl_mem_cocompact)] with z hz ha hnz
  have hn : z ≠ 0 := hnz
  have han : AnalyticAt ℂ (fun z : ℂ => z⁻¹ * A z⁻¹) z :=
    (analyticAt_inv hn).mul (ha.comp (analyticAt_inv hn))
  have hcd : ContDiffAt ℂ n (fun z : ℂ => z⁻¹ * A z⁻¹) z := han.contDiffAt
  have hb := Complex.reCLM.norm_iteratedFDeriv_comp_left
    (hcd.restrict_scalars ℝ) le_rfl
  rw [← hcd.restrictScalars_iteratedFDeriv (𝕜 := ℝ), Function.comp_apply,
    ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hb
  calc
    _ ≤ ‖Complex.reCLM‖ * ‖iteratedDeriv n (fun z : ℂ => z⁻¹ * A z⁻¹) z‖ := hb
    _ ≤ ‖Complex.reCLM‖ * (C * ‖z‖⁻¹ ^ (n+1)) :=
      mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    _ = _ := by ring

lemma eventual_representation_derivative_decay {u : ℂ → ℝ} {A : ℂ → ℂ}
    (hA : AnalyticAt ℂ A 0)
    (hu : ∀ᶠ z in cocompact ℂ, u z = (z⁻¹*A z⁻¹).re) (n : ℕ) :
    ∃ C : ℝ, ∀ᶠ z in cocompact ℂ,
      ‖iteratedFDeriv ℝ n u z‖ ≤ C * ‖z‖⁻¹ ^ (n+1) := by
  obtain ⟨C, hC⟩ := real_part_inverse_derivative_decay hA n
  refine ⟨C, ?_⟩
  filter_upwards [eventually_nhds_of_cocompact hu, hC] with z hz hcz
  have he := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hz n).eq_of_nhds
  rwa [he]

theorem projection_has_normalized_exterior_potential (e : PlaneL2) {R : ℝ}
    (he : ∀ᵐ x ∂volume, R < ‖x‖ → e x = 0) :
    ∃ φ : ℂ → ℝ,
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
        SobolevOn φ (compactGradientProjection e) S) ∧
      ContDiffOn ℝ ∞ φ {z | R < ‖z‖} ∧ HarmonicOnNhd φ {z | R < ‖z‖} ∧
      (∀ᵐ x ∂volume, R < ‖x‖ → gradient φ x = compactGradientProjection e x) ∧
      Tendsto φ (cocompact ℂ) (𝓝 0) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ z in cocompact ℂ,
        ‖iteratedFDeriv ℝ k φ z‖ ≤ C * ‖z‖⁻¹ ^ (k+1)) := by
  obtain ⟨φ,hφ,hs,hh,hg⟩ := projection_has_classical_harmonic_potential e
    (isOpen_lt continuous_const continuous_norm) he
  obtain ⟨A,c,hA,hr⟩ := finite_energy_harmonic_exterior_representation hh (Lp.memLp _) hg
  refine ⟨(fun z => φ z - c), (fun S hS hb => (hφ S hS hb).sub_const hb c),
    hs.sub contDiffOn_const, hh.sub (harmonicOnNhd_const c), ?_, ?_,
    eventual_representation_derivative_decay hA hr⟩
  · filter_upwards [hg] with z hz
    simpa only [gradient, fderiv_sub_const] using hz
  · have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
      simpa [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
    have ht := Complex.continuous_re.continuousAt.tendsto.comp
      (hi.mul (hA.continuousAt.tendsto.comp hi))
    apply (show Tendsto (fun z : ℂ => (z⁻¹ * A z⁻¹).re) (cocompact ℂ) (𝓝 0) from by
      simpa only [Function.comp_def, zero_mul, Complex.zero_re] using ht).congr'
    exact Filter.EventuallyEq.symm hr

theorem compact_projection_sobolev {A : Set ℂ} {h : ℂ → ℝ} {e : ℂ → ℂ}
    (hA : IsCompact A) (hA0 : volume A = 0) (hh : SobolevOn h e Aᶜ)
    (hc : IsCompact (essentialSupport h)) :
    ∃ he : MemLp e 2 volume, ∃ φ F : ℂ → ℝ, ∃ R : ℝ,
      0 < R ∧
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
        SobolevOn φ (compactGradientProjection (he.toLp e)) S) ∧
      F =ᵐ[volume] h - φ ∧
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
        SobolevOn F (compactJumpField (he.toLp e)) (S \ A)) ∧
      ContDiffOn ℝ ∞ F {z | R < ‖z‖} ∧ HarmonicOnNhd F {z | R < ‖z‖} ∧
      (∀ᵐ x ∂volume, R < ‖x‖ → gradient F x = compactJumpField (he.toLp e) x) ∧
      Tendsto φ (cocompact ℂ) (𝓝 0) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ z in cocompact ℂ,
        ‖iteratedFDeriv ℝ k F z‖ ≤ C * ‖z‖⁻¹ ^ (k+1)) := by
  classical
  have hmu : volume.restrict Aᶜ = volume :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr hA0)
  have he : MemLp e 2 volume := by simpa [hmu] using hh.2.1
  obtain ⟨R0,hR0,he0⟩ := compact_support_weak_gradient hA hh hc
  have heL : ∀ᵐ x ∂volume, R0 < ‖x‖ → (he.toLp e) x = 0 := by
    filter_upwards [he.coeFn_toLp, he0] with x hx hz
    simpa [hx] using hz
  obtain ⟨φ,hφ,hφs,hφh,hφg,hφt,hφd⟩ := projection_has_normalized_exterior_potential (he.toLp e) heL
  obtain ⟨R1,hR1,hb⟩ := hc.isBounded.exists_pos_norm_lt
  let R := max R0 R1
  let h0 := (essentialSupport h).indicator h
  let F := fun x => h0 x - φ x
  have hh0 : h0 =ᵐ[volume] h := by
    exact indicator_ae_eq_of_restrict_compl_ae_eq_zero
      (isClosed_essentialSupport h).measurableSet (ae_zero_compl_essentialSupport h)
  have hFeq : F =ᵐ[volume] h - φ := by
    filter_upwards [hh0] with x hx
    exact congrArg (fun t => t - φ x) hx
  have hFeq' : EqOn F (-φ) {z : ℂ | R < ‖z‖} := by
    intro z hz
    have hznot : z ∉ essentialSupport h := by
      intro hzs
      have := hb z hzs
      have : R1 < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz
      linarith [hb z hzs]
    simp [F, h0, Set.indicator_of_notMem hznot]
  have hRsub : {z : ℂ | R < ‖z‖} ⊆ {z | R0 < ‖z‖} := by
    intro z hz
    exact lt_of_le_of_lt (le_max_left R0 R1) (show max R0 R1 < ‖z‖ from hz)
  refine ⟨he, φ, F, R, lt_of_lt_of_le hR0 (le_max_left _ _), hφ, hFeq, ?_, ?_, ?_, ?_,hφt,?_⟩
  · intro S hS hbS
    have hhs := hh.mono (show S \ A ⊆ Aᶜ from fun _ hx => hx.2)
    have hfs := (hφ S hS hbS).mono (show S \ A ⊆ S from sdiff_subset)
    have hgrad : (e - compactGradientProjection (he.toLp e) : ℂ → ℂ) =ᵐ[volume]
        compactJumpField (he.toLp e) := by
      filter_upwards [he.coeFn_toLp, Lp.coeFn_sub (he.toLp e) (compactGradientProjection (he.toLp e))]
        with x hx hy
      simpa only [compactJumpField, Pi.sub_apply, hx] using hy.symm
    exact ((hhs.sub hfs).congr_ae hFeq).congr_gradient (ae_restrict_of_ae hgrad)
  · apply (hφs.mono hRsub).neg.congr
    exact hFeq'
  · intro z hz
    have hn : F =ᶠ[𝓝 z] -φ := hFeq'.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
    exact (harmonicAt_congr_nhds hn).mpr ((hφh z (hRsub hz)).neg)
  · filter_upwards [heL,hφg,Lp.coeFn_sub (he.toLp e) (compactGradientProjection (he.toLp e))]
      with z hez hg hp hz
    have hz0 : R0 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
    have hn : F =ᶠ[𝓝 z] -φ := hFeq'.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
    rw [show gradient F z = -gradient φ z by
      simp only [gradient, hn.fderiv_eq, fderiv_neg, map_neg]]
    simp only [compactJumpField, hp, Pi.sub_apply, hez hz0, zero_sub, hg hz0]
  · intro k
    obtain ⟨C,hC⟩ := hφd k
    refine ⟨C,?_⟩
    have hext : ∀ᶠ z : ℂ in cocompact ℂ, R < ‖z‖ := by
      have hh := (isCompact_closedBall (0 : ℂ) R).compl_mem_cocompact
      filter_upwards [hh] with z hz
      simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hz
    filter_upwards [hC,hext] with z hz hcZ
    have hn : F =ᶠ[𝓝 z] -φ := hFeq'.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hcZ)
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hn k).eq_of_nhds]
    simpa only [iteratedFDeriv_neg, Pi.neg_apply, norm_neg] using hz

theorem projection_has_testable_normalized_exterior_potential (e : PlaneL2) {R : ℝ}
    (he : ∀ᵐ x ∂volume, R < ‖x‖ → e x = 0) :
    ∃ φ : ℂ → ℝ,
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
        SobolevOn φ (compactGradientProjection e) S) ∧
      CompactDivergenceTestable φ (compactGradientProjection e) ∧
      ContDiffOn ℝ ∞ φ {z | R < ‖z‖} ∧ HarmonicOnNhd φ {z | R < ‖z‖} ∧
      (∀ᵐ x ∂volume, R < ‖x‖ → gradient φ x = compactGradientProjection e x) ∧
      Tendsto φ (cocompact ℂ) (𝓝 0) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ z in cocompact ℂ,
        ‖iteratedFDeriv ℝ k φ z‖ ≤ C * ‖z‖⁻¹ ^ (k+1)) := by
  obtain ⟨u,huT,hu⟩ := gradient_closure_has_testable_local_potential
    (compactGradientClosure.starProjection_apply_mem e)
  have hO : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨φ,hv,hs,hh⟩ := weak_harmonic_regular
    (locallyIntegrable_of_local_sobolev hu) hO (projected_potential_weak_harmonic hu he)
  have hφ (S : Set ℂ) (hS : IsOpen S) (hb : Bornology.IsBounded S) :
      SobolevOn φ (compactGradientProjection e) S := (hu S hS hb).congr_ae hv
  have hφT := huT.congr_ae hv.symm
  have hg := local_smooth_weak_gradient_ae hφ (Lp.memLp _) hO hs
  obtain ⟨A,c,hA,hr⟩ := finite_energy_harmonic_exterior_representation hh (Lp.memLp _) hg
  refine ⟨(fun z => φ z - c), (fun S hS hb => (hφ S hS hb).sub_const hb c),
    hφT.sub_const (fun S hS hb => (hφ S hS hb).1) c,
    hs.sub contDiffOn_const, hh.sub (harmonicOnNhd_const c), ?_, ?_,
    eventual_representation_derivative_decay hA hr⟩
  · filter_upwards [hg] with z hz
    simpa only [gradient, fderiv_sub_const] using hz
  · have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
      simpa [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
    have ht := Complex.continuous_re.continuousAt.tendsto.comp
      (hi.mul (hA.continuousAt.tendsto.comp hi))
    apply (show Tendsto (fun z : ℂ => (z⁻¹ * A z⁻¹).re) (cocompact ℂ) (𝓝 0) from by
      simpa only [Function.comp_def, zero_mul, Complex.zero_re] using ht).congr'
    exact Filter.EventuallyEq.symm hr

end MumfordShah
end

end OAI
