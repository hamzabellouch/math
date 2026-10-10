import Mathlib
import OAI.Analysis.MumfordShah.DecayComparison
import OAI.Analysis.MumfordShah.ProjectionPairing

namespace OAI

/-! MumfordShah harmonic analysis. -/

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

def complexPartial (f : ℂ → ℝ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 : ℂ) - I * (fderiv ℝ f z I : ℂ)

lemma directional_eq_re_mul_complexPartial (f : ℂ → ℝ) (z n : ℂ) :
    fderiv ℝ f z n = (n * complexPartial f z).re := by
  have hn : n = n.re • (1 : ℂ) + n.im • I := by
    apply Complex.ext <;> simp
  calc
    fderiv ℝ f z n = fderiv ℝ f z (n.re • (1 : ℂ) + n.im • I) :=
      congrArg (fderiv ℝ f z) hn
    _ = n.re * fderiv ℝ f z 1 + n.im * fderiv ℝ f z I := by
      rw [map_add, map_smul, map_smul]
      rfl
    _ = (n * complexPartial f z).re := by simp [complexPartial]

theorem harmonic_fderiv_eq_of_directional_constant
    {O : Set ℂ} (_hO : IsOpen O) (hOc : IsConnected O)
    {f : ℂ → ℝ} (hf : HarmonicOnNhd f O)
    {z₀ : ℂ} (hz₀ : z₀ ∈ O) {r : ℝ} (hr : 0 < r)
    (hball : ball z₀ r ⊆ O) {n : ℂ} (hn : n ≠ 0) {c : ℝ}
    (hc : ∀ z ∈ ball z₀ r, fderiv ℝ f z n = c) :
    ∀ z ∈ O, fderiv ℝ f z = fderiv ℝ f z₀ := by
  have hpart : AnalyticOnNhd ℂ (complexPartial f) O :=
    fun z hz => HarmonicAt.analyticAt_complex_partial (hf z hz)
  have hnp : AnalyticOnNhd ℂ (fun z => n * complexPartial f z) (ball z₀ r) :=
    fun z hz => analyticAt_const.mul (hpart z (hball hz))
  have hre : ∀ z ∈ ball z₀ r, (n * complexPartial f z).re = c := by
    intro z hz
    rw [← directional_eq_re_mul_complexPartial]
    exact hc z hz
  obtain ⟨d, hd⟩ := hnp.eq_const_of_re_eq_const hre isOpen_ball
    ((convex_ball z₀ r).isConnected ⟨z₀, mem_ball_self hr⟩)
  have hlocal : complexPartial f =ᶠ[𝓝 z₀] fun _ => complexPartial f z₀ := by
    filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz
    apply mul_left_cancel₀ hn
    exact (hd z hz).trans (hd z₀ (mem_ball_self hr)).symm
  have hall := hpart.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    hOc.isPreconnected hz₀ hlocal
  intro z hz
  apply ContinuousLinearMap.ext
  intro a
  rw [directional_eq_re_mul_complexPartial, directional_eq_re_mul_complexPartial,
    hall hz]

theorem harmonic_affine_of_directional_constant
    {O : Set ℂ} (hO : IsOpen O) (hOc : IsConnected O)
    {f : ℂ → ℝ} (hf : HarmonicOnNhd f O)
    {z₀ : ℂ} (hz₀ : z₀ ∈ O) {r : ℝ} (hr : 0 < r)
    (hball : ball z₀ r ⊆ O) {n : ℂ} (hn : n ≠ 0) {c : ℝ}
    (hc : ∀ z ∈ ball z₀ r, fderiv ℝ f z n = c) :
    ∃ L : ℂ →L[ℝ] ℝ, ∃ b : ℝ, ∀ z ∈ O, f z = L z + b := by
  let L := fderiv ℝ f z₀
  have hder := harmonic_fderiv_eq_of_directional_constant hO hOc hf hz₀ hr hball hn hc
  have hdiff : DifferentiableOn ℝ f O :=
    fun z hz => ((hf z hz).1.differentiableAt (by norm_num)).differentiableWithinAt
  obtain ⟨b, hb⟩ := hO.exists_eq_add_of_fderiv_eq hOc.isPreconnected hdiff
    L.differentiable.differentiableOn (by
      intro z hz
      simpa only [ContinuousLinearMap.fderiv] using hder z hz)
  exact ⟨L, b, hb⟩

theorem harmonic_eq_of_minimum_on_ball {J : ℂ → ℝ} {r : ℝ}
    (hr : 0 < r) (hJ : HarmonicOnNhd J (ball 0 r))
    (hmin : ∀ t ∈ ball 0 r, J 0 ≤ J t) :
    ∀ t ∈ ball 0 r, J t = J 0 := by
  obtain ⟨F, hF, hre⟩ := hJ.exists_analyticOnNhd_ball_re_eq
  rcases hF.is_constant_or_isOpen (convex_ball (0 : ℂ) r).isPreconnected with
    hconst | hopen
  · obtain ⟨c, hc⟩ := hconst
    intro t ht
    calc
      J t = (F t).re := (hre ht).symm
      _ = (F 0).re := congrArg Complex.re ((hc t ht).trans (hc 0 (mem_ball_self hr)).symm)
      _ = J 0 := hre (mem_ball_self hr)
  · have hFi : IsOpen (F '' ball 0 r) := hopen _ Subset.rfl isOpen_ball
    have h0 : F 0 ∈ F '' ball 0 r := mem_image_of_mem F (mem_ball_self hr)
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hFi (F 0) h0
    have hz : F 0 - (ε / 2 : ℝ) ∈ ball (F 0) ε := by
      rw [mem_ball_iff_norm]
      norm_num [sub_sub_cancel_left, Complex.norm_real, abs_of_pos (half_pos hε), abs_of_pos hε]
      linarith
    obtain ⟨t, ht, heq⟩ := hb hz
    have hret := congrArg Complex.re heq
    simp only [Complex.sub_re, Complex.ofReal_re, hre ht,
      hre (mem_ball_self hr)] at hret
    have hmt := hmin t ht
    linarith

theorem translated_energy_forces_constant_interactions
    {Ip Iq : ℂ → ℝ} {r pq qq : ℝ} (hr : 0 < r)
    (hIp : HarmonicOnNhd Ip (ball 0 r))
    (henergy : ∀ t ∈ ball 0 r, ∀ σ : ℝ,
      0 ≤ 2 * (Ip t - Ip 0) + 2 * σ * (Iq t + pq) + σ ^ 2 * qq) :
    (∀ t ∈ ball 0 r, Ip t = Ip 0) ∧
      ∀ t ∈ ball 0 r, Iq t = -pq := by
  have hconst := harmonic_eq_of_minimum_on_ball hr hIp (by
    intro t ht
    have h := henergy t ht 0
    linarith)
  refine ⟨hconst, ?_⟩
  intro t ht
  have hlin : Iq t + pq = 0 := linear_coefficient_eq_zero (by
    intro σ
    simpa only [hconst t ht, sub_self, mul_zero, zero_add] using henergy t ht σ)
  linarith

theorem continuous_eq_zero_of_smooth_tests {I : Set ℝ} (hI : IsOpen I)
    {a : ℝ → ℝ} (ha : ContinuousOn a I)
    (htest : ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β →
      tsupport β ⊆ I → (∫ s, β s * a s) = 0) :
    ∀ s ∈ I, a s = 0 := by
  have hae : ∀ᵐ s ∂MeasureTheory.volume, s ∈ I → a s = 0 :=
    hI.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (ha.locallyIntegrableOn hI.measurableSet) (by
        intro β hβ hβc hβI
        simpa only [smul_eq_mul] using htest β hβ hβc hβI)
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq
    ((MeasureTheory.ae_restrict_iff' hI.measurableSet).2 hae) hI ha continuousOn_const

theorem harmonic_affine_of_jump_tests
    {O : Set ℂ} (hO : IsOpen O) (hOc : IsConnected O)
    {f : ℂ → ℝ} (hf : HarmonicOnNhd f O)
    {I : Set ℝ} (hI : IsOpen I) {s₀ : ℝ} (hs₀ : s₀ ∈ I)
    {γ n : ℝ → ℂ} {w : ℝ → ℝ}
    (hγ : ContinuousOn γ I) (hnc : ContinuousOn n I) (hwc : ContinuousOn w I)
    (hn : n s₀ ≠ 0) (hw : w s₀ ≠ 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hplace : ∀ s ∈ I, ∀ t ∈ ball (0 : ℂ) δ, γ s + t ∈ O)
    (htest : ∀ t ∈ ball (0 : ℂ) δ,
      ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ I →
      (∫ s, β s * ((fderiv ℝ f (γ s + t) (n s) -
        fderiv ℝ f (γ s) (n s)) * w s)) = 0) :
    ∃ L : ℂ →L[ℝ] ℝ, ∃ b : ℝ, ∀ z ∈ O, f z = L z + b := by
  have hgrad : ContinuousOn (fderiv ℝ f) O :=
    hf.contDiffOn.continuousOn_fderiv_of_isOpen hO (by norm_num)
  have hγO : MapsTo γ I O := by
    intro s hs
    simpa only [add_zero] using hplace s hs 0 (mem_ball_self hδ)
  have heq : ∀ t ∈ ball (0 : ℂ) δ,
      fderiv ℝ f (γ s₀ + t) (n s₀) = fderiv ℝ f (γ s₀) (n s₀) := by
    intro t ht
    have htrans : ContinuousOn (fun s => fderiv ℝ f (γ s + t) (n s)) I :=
      (hgrad.comp (hγ.add continuousOn_const) (fun s hs => hplace s hs t ht)).clm_apply hnc
    have hbase : ContinuousOn (fun s => fderiv ℝ f (γ s) (n s)) I :=
      (hgrad.comp hγ hγO).clm_apply hnc
    have hzero := continuous_eq_zero_of_smooth_tests hI
      ((htrans.sub hbase).mul hwc) (htest t ht) s₀ hs₀
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hw)
  have hball : ball (γ s₀) δ ⊆ O := by
    intro z hz
    have ht : z - γ s₀ ∈ ball (0 : ℂ) δ := by
      simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hz
    simpa only [add_sub_cancel] using hplace s₀ hs₀ (z - γ s₀) ht
  apply harmonic_affine_of_directional_constant hO hOc hf (hγO hs₀) hδ hball hn
  intro z hz
  have ht : z - γ s₀ ∈ ball (0 : ℂ) δ := by
    simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hz
  simpa only [add_sub_cancel] using heq (z - γ s₀) ht

theorem constant_field_eq_zero_of_linear_energy_growth
    {G : ℂ → ℂ} {c : ℂ} (hG : G =ᵐ[volume] fun _ => c)
    {C : ℝ} (hgrowth : ∀ R : ℝ, 1 ≤ R →
      (∫ x in ball (0 : ℂ) R, ‖G x‖ ^ 2) ≤ C * (1 + R)) : c = 0 := by
  by_contra hc
  have ha : 0 < Real.pi * ‖c‖ ^ 2 :=
    mul_pos Real.pi_pos (sq_pos_of_pos (norm_pos_iff.mpr hc))
  obtain ⟨R, hR⟩ := exists_gt (max 1 (2 * |C| / (Real.pi * ‖c‖ ^ 2)))
  have hR1 : 1 < R := (le_max_left _ _).trans_lt hR
  have hR0 : 0 < R := lt_trans zero_lt_one hR1
  have hRa : 2 * |C| < R * (Real.pi * ‖c‖ ^ 2) :=
    (div_lt_iff₀ ha).mp ((le_max_right _ _).trans_lt hR)
  have hint : (∫ x in ball (0 : ℂ) R, ‖G x‖ ^ 2) =
      R ^ 2 * Real.pi * ‖c‖ ^ 2 := by
    calc
      (∫ x in ball (0 : ℂ) R, ‖G x‖ ^ 2) =
          ∫ _ in ball (0 : ℂ) R, ‖c‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hG] with x hx
        rw [hx]
      _ = R ^ 2 * Real.pi * ‖c‖ ^ 2 := by
        simp [Measure.real, ENNReal.toReal_mul,
          ENNReal.toReal_pow, ENNReal.toReal_ofReal hR0.le]
  have hbound := hgrowth R hR1.le
  rw [hint] at hbound
  have hC : C * (1 + R) ≤ |C| * (1 + R) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  have hC2 : |C| * (1 + R) ≤ 2 * |C| * R := by
    nlinarith [abs_nonneg C]
  have hbad := mul_lt_mul_of_pos_right hRa hR0
  nlinarith

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

lemma integrableOn_mul_continuousOn_compact {K : Set ℂ} (hK : IsCompact K)
    {e F : ℂ → ℂ} (he : IntegrableOn e K volume) (hF : ContinuousOn F K) :
    IntegrableOn (fun x => e x*F x) K volume := by
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hF
  apply (he.norm.const_mul M).mono' (he.aestronglyMeasurable.mul (hF.aestronglyMeasurable hK.measurableSet))
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  change ‖e x*F x‖ ≤ M*‖e x‖
  rw [norm_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hM x hx) (norm_nonneg (e x))

theorem analytic_compact_translation_integral {K O : Set ℂ} (hK : IsCompact K)
    {F e : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F O) (he : IntegrableOn e K volume)
    {r : ℝ} (hKO : ∀ x ∈ K, ∀ t ∈ closedBall (0:ℂ) r, x+t ∈ O) :
    AnalyticOnNhd ℂ (fun t => ∫ x in K, e x*F (x+t)) (ball (0:ℂ) r) := by
  let L := (fun z : ℂ × ℂ => z.1+z.2) '' (K ×ˢ closedBall (0:ℂ) r)
  have hL : IsCompact L := (hK.prod (isCompact_closedBall (0:ℂ) r)).image (continuous_fst.add continuous_snd)
  have hLO : L ⊆ O := by rintro z ⟨⟨x,t⟩,⟨hx,ht⟩,rfl⟩; exact hKO x hx t ht
  have hFL : AnalyticOnNhd ℂ F L := hF.mono hLO
  obtain ⟨M,hM⟩ := hL.exists_bound_of_continuousOn hFL.deriv.continuousOn
  have hFc (t : ℂ) (ht : t ∈ ball (0:ℂ) r) : ContinuousOn (fun x => F (x+t)) K :=
    hF.continuousOn.comp (continuous_id.add continuous_const).continuousOn
      (fun x hx => hKO x hx t (ball_subset_closedBall ht))
  have hFd (t : ℂ) (ht : t ∈ ball (0:ℂ) r) : ContinuousOn (fun x => deriv F (x+t)) K :=
    hF.deriv.continuousOn.comp (continuous_id.add continuous_const).continuousOn
      (fun x hx => hKO x hx t (ball_subset_closedBall ht))
  have hi t ht := integrableOn_mul_continuousOn_compact hK he (hFc t ht)
  have hid t ht := integrableOn_mul_continuousOn_compact hK he (hFd t ht)
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro t ht
  have hs : ball (0:ℂ) r ∈ 𝓝 t := isOpen_ball.mem_nhds ht
  have hm : ∀ᶠ y in 𝓝 t, AEStronglyMeasurable (fun x => e x*F (x+y)) (volume.restrict K) :=
    Filter.Eventually.mono hs (fun y hy => (hi y hy).aestronglyMeasurable)
  have hb : ∀ᵐ x ∂volume.restrict K, ∀ y ∈ ball (0:ℂ) r,
      ‖e x*deriv F (x+y)‖ ≤ M*‖e x‖ := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx y hy
    rw [norm_mul]
    have hh : x+y ∈ L := ⟨(x,y),⟨hx,ball_subset_closedBall hy⟩,rfl⟩
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hM _ hh) (norm_nonneg (e x))
  have hd : ∀ᵐ x ∂volume.restrict K, ∀ y ∈ ball (0:ℂ) r,
      HasDerivAt (fun y => e x*F (x+y)) (e x*deriv F (x+y)) y := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx y hy
    have hh := (hF (x+y) (hKO x hx y (ball_subset_closedBall hy))).differentiableAt.hasDerivAt
    simpa only [mul_one, Function.comp_def] using (hh.comp y ((hasDerivAt_id y).const_add x)).const_mul (e x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm (hi t ht)
    (hid t ht).aestronglyMeasurable hb (he.norm.const_mul M) hd).2.differentiableAt.differentiableWithinAt

theorem harmonic_compact_gradient_interaction {K O : Set ℂ} (hK : IsCompact K)
    {f : ℂ → ℝ} (hf : HarmonicOnNhd f O) {e : ℂ → ℂ} (he : IntegrableOn e K volume)
    {r : ℝ} (hKO : ∀ x ∈ K, ∀ t ∈ closedBall (0:ℂ) r, x+t ∈ O) :
    HarmonicOnNhd (fun t => ∫ x in K, inner ℝ (gradient f (x+t)) (e x)) (ball (0:ℂ) r) := by
  have hF : AnalyticOnNhd ℂ (complexPartial f) O := fun z hz => HarmonicAt.analyticAt_complex_partial (hf z hz)
  have hJ := analytic_compact_translation_integral hK hF he hKO
  have heq : EqOn (fun t => (∫ x in K, e x*complexPartial f (x+t)).re)
      (fun t => ∫ x in K, inner ℝ (gradient f (x+t)) (e x)) (ball (0:ℂ) r) := by
    intro t ht
    have hc : ContinuousOn (fun x => complexPartial f (x+t)) K :=
      hF.continuousOn.comp (continuous_id.add continuous_const).continuousOn
        (fun x hx => hKO x hx t (ball_subset_closedBall ht))
    change RCLike.re (∫ x in K, e x*complexPartial f (x+t)) = _
    rw [← integral_re (integrableOn_mul_continuousOn_compact hK he hc)]
    apply integral_congr_ae
    filter_upwards with x
    rw [inner_gradient_left,directional_eq_re_mul_complexPartial]
    rfl
  intro t ht
  exact (harmonicAt_congr_nhds (Filter.Eventually.mono (isOpen_ball.mem_nhds ht)
    (fun y hy => heq hy))).mp (hJ t ht).harmonicAt_re

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

lemma weak_gradient_zero_off_compact_support {A : Set ℂ} {h : ℂ → ℝ} {e : ℂ → ℂ}
    (hA : IsCompact A) (hh : SobolevOn h e Aᶜ) (hc : IsCompact (essentialSupport h)) :
    ∀ᵐ x ∂volume, x ∉ A ∪ essentialSupport h → e x = 0 := by
  have he := weak_gradient_zero_on (hh.mono (show (A ∪ essentialSupport h)ᶜ ⊆ Aᶜ from
    fun x hx hxA => hx (Or.inl hxA))) (hA.union hc).isClosed.isOpen_compl
    (ae_restrict_of_ae_restrict_of_subset (show (A ∪ essentialSupport h)ᶜ ⊆ (essentialSupport h)ᶜ from
      fun x hx hxe => hx (Or.inr hxe)) (ae_zero_compl_essentialSupport h))
  exact (ae_restrict_iff' (hA.union hc).isClosed.isOpen_compl.measurableSet).mp he

lemma compact_tube_inside {K O : Set ℂ} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ K, ∀ t ∈ closedBall (0:ℂ) r, x+t ∈ O := by
  obtain ⟨r,hr,hsub⟩ := hK.exists_cthickening_subset_open hO hKO
  refine ⟨r,hr,?_⟩
  intro x hx t ht
  apply hsub
  apply mem_cthickening_of_dist_le (x+t) x r K hx
  simpa only [mem_closedBall,dist_zero_right,dist_eq_norm,add_sub_cancel_left,sub_zero] using ht

theorem harmonic_translated_compact_source {K O : Set ℂ} (hK : IsCompact K)
    {f : ℂ → ℝ} (hf : HarmonicOnNhd f O) {G e : ℂ → ℂ}
    (hGeq : ∀ᵐ x ∂volume, x ∈ O → G x = gradient f x)
    (he : MemLp e 2 volume) (he0 : ∀ᵐ x ∂volume, x ∉ K → e x = 0)
    {r : ℝ} (hKO : ∀ x ∈ K, ∀ t ∈ closedBall (0:ℂ) r, x+t ∈ O) :
    HarmonicOnNhd (fun t => ∫ x : ℂ, inner ℝ (G x) (e (x-t))) (ball (0:ℂ) r) := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hharm := harmonic_compact_gradient_interaction hK hf ((he.restrict K).integrable (by norm_num)) hKO
  have heq : EqOn (fun t => ∫ x : ℂ, inner ℝ (G x) (e (x-t)))
      (fun t => ∫ x in K, inner ℝ (gradient f (x+t)) (e x)) (ball (0:ℂ) r) := by
    intro t ht
    dsimp only
    rw [← (measurePreserving_add_right (volume : Measure ℂ) t).integral_comp
      (Homeomorph.addRight t).measurableEmbedding (fun x => inner ℝ (G x) (e (x-t)))]
    simp only [add_sub_cancel_right]
    rw [← setIntegral_eq_integral_of_ae_compl_eq_zero (s := K) (by
      filter_upwards [he0] with x hx hxx
      rw [hx hxx,inner_zero_right])]
    apply integral_congr_ae
    have hg := (measurePreserving_add_right (volume : Measure ℂ) t).quasiMeasurePreserving.ae hGeq
    filter_upwards [ae_restrict_of_ae hg,ae_restrict_mem hK.measurableSet] with x hx hxK
    rw [hx (hKO x hxK t (ball_subset_closedBall ht))]
  intro t ht
  exact (harmonicAt_congr_nhds (heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds ht))).mpr (hharm t ht)

lemma testable_inverse_decay_pairing_zero {φ : ℂ → ℝ} {w : PlaneL2} {G : ℂ → ℂ}
    (htest : CompactDivergenceTestable φ w)
    (hφ : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → MemLp φ 2 (volume.restrict U))
    (hG : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → MemLp G 2 (volume.restrict U))
    (hdiv : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      (∫ x : ℂ, inner ℝ (G x) (gradient η x)) = 0)
    (hφD : HasInversePowerDecay φ 1) (hwD : HasInversePowerDecay (fun x => w x) 2)
    {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ R : ℝ, 1 ≤ R → (∫ x in ball (0:ℂ) R, ‖G x‖^2) ≤ C*(1+R)) (t : ℂ) :
    (∫ x : ℂ, inner ℝ (G x) (w (x-t))) = 0 := by
  obtain ⟨D,R,hD,hR,hφD⟩ := hφD
  obtain ⟨E,S,hE,hS,hwD⟩ := hwD
  apply translated_projection_pairing_zero htest hφ hG hdiv hC hD hE
    (hR.trans (le_max_left R S)) hg
  · filter_upwards [hφD] with x hx hxx
    simpa only [Real.norm_eq_abs,pow_one] using hx ((le_max_left _ _).trans hxx)
  · filter_upwards [hwD] with x hx hxx
    exact hx ((le_max_right _ _).trans hxx)

lemma remove_testable_projection_interaction {φ : ℂ → ℝ} {w : PlaneL2} {G e : ℂ → ℂ}
    (htest : CompactDivergenceTestable φ w)
    (hφ : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → MemLp φ 2 (volume.restrict U))
    (hG : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → MemLp G 2 (volume.restrict U))
    (hdiv : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      (∫ x : ℂ, inner ℝ (G x) (gradient η x)) = 0)
    (he : MemLp e 2 volume) (heD : HasInversePowerDecay e 2)
    (hφD : HasInversePowerDecay φ 1) (hwD : HasInversePowerDecay (fun x => w x) 2)
    {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ R : ℝ, 1 ≤ R → (∫ x in ball (0:ℂ) R, ‖G x‖^2) ≤ C*(1+R)) (t : ℂ) :
    (∫ x : ℂ, inner ℝ (G x) (e (x-t)-w (x-t))) =
      (∫ x : ℂ, inner ℝ (G x) (e (x-t))) := by
  simp_rw [inner_sub_right]
  rw [integral_sub ((heD.translate t).integrable_inner (memLp_plane_translate he t) hG hC hg)
    ((hwD.translate t).integrable_inner (memLp_plane_translate (Lp.memLp w) t) hG hC hg),
    testable_inverse_decay_pairing_zero htest hφ hG hdiv hφD hwD hC hg t,sub_zero]

end MumfordShah
end

end OAI
