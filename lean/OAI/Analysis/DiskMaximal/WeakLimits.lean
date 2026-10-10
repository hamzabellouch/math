import OAI.Analysis.DiskMaximal.Approximation

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace WeakCompact
open CompactlySupported CompactlySupportedContinuousMap

/-- A single free ultrafilter furnishes simultaneous weak limits; no sequence
of gradients or a Radon representation is being added as an assumption. -/
lemma bounded_tendsto {a : ℕ → ℝ} {B : ℝ} (hb : ∀ n, |a n| ≤ B) :
    Tendsto a (hyperfilter ℕ) (𝓝 (limUnder (hyperfilter ℕ) a)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨x,hx,hj⟩ := isCompact_Icc.ultrafilter_le_nhds
    ((hyperfilter ℕ).map a) (by
      change Filter.map a (hyperfilter ℕ) ≤ 𝓟 (Icc (-B) B)
      rw [le_principal_iff]
      change ∀ᶠ n : ℕ in hyperfilter ℕ, a n ∈ Icc (-B) B
      exact Eventually.of_forall (fun n => abs_le.mp (hb n)))
  exact ⟨x,hj⟩

variable {X : Type*} [TopologicalSpace X]
    (Λ : ℕ → (C_c(X, ℝ) →ₚ[ℝ] ℝ)) {B : ℝ}
    (hb : ∀ n (f : C_c(X, ℝ)), |Λ n f| ≤ B*‖f.toBoundedContinuousFunction‖)

def limitValue (f : C_c(X, ℝ)) : ℝ := limUnder (hyperfilter ℕ) (fun n => Λ n f)

include hb

lemma limit_tendsto (f : C_c(X, ℝ)) :
    Tendsto (fun n => Λ n f) (hyperfilter ℕ) (𝓝 (limitValue Λ f)) := bounded_tendsto (fun n => hb n f)

def limitPositive : C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toFun := limitValue Λ
  map_add' f g := tendsto_nhds_unique (limit_tendsto Λ hb (f+g))
    (by simpa only [map_add] using (limit_tendsto Λ hb f).add (limit_tendsto Λ hb g))
  map_smul' c f := tendsto_nhds_unique (limit_tendsto Λ hb (c • f))
    (by simpa only [map_smul, smul_eq_mul, RingHom.id_apply] using (limit_tendsto Λ hb f).const_mul c)
  monotone' := by
    intro f g hfg
    exact le_of_tendsto_of_tendsto (limit_tendsto Λ hb f) (limit_tendsto Λ hb g)
      (Eventually.of_forall (fun n => (Λ n).mono hfg))

lemma limit_bound (f : C_c(X, ℝ)) : |limitPositive Λ hb f| ≤ B*‖f.toBoundedContinuousFunction‖ :=
  le_of_tendsto (limit_tendsto Λ hb f).abs (Eventually.of_forall (fun n => hb n f))

variable [T2Space X] [MeasurableSpace X] [BorelSpace X] [LocallyCompactSpace X]

def limitMeasure : Measure X := RealRMK.rieszMeasure (limitPositive Λ hb)

lemma integral_limitMeasure (f : C_c(X, ℝ)) :
    Tendsto (fun n => Λ n f) (hyperfilter ℕ) (𝓝 (∫ x, f x ∂limitMeasure Λ hb)) := by
  rw [limitMeasure,RealRMK.integral_rieszMeasure]
  exact limit_tendsto Λ hb f

lemma limitMeasure_compact_bound (hB : 0 ≤ B) {K : Set X} (hK : IsCompact K) :
    limitMeasure Λ hb K ≤ ENNReal.ofReal B := by
  obtain ⟨f,hf1,hfc,-,hf⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  let f' : C_c(X, ℝ) := ⟨f,hfc⟩
  have hm := RealRMK.rieszMeasure_le_of_eq_one (limitPositive Λ hb) (f := f') (fun x => (hf x).1) hK hf1
  have hn : ‖f'.toBoundedContinuousFunction‖ ≤ 1 := by
    apply (BoundedContinuousFunction.norm_le (by norm_num)).mpr
    intro x
    change ‖f x‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (hf x).1]
    exact (hf x).2
  have he : limitPositive Λ hb f' ≤ B :=
    (le_abs_self _).trans ((limit_bound Λ hb f').trans ((mul_le_mul_of_nonneg_left hn hB).trans_eq (mul_one B)))
  exact hm.trans (ENNReal.ofReal_le_ofReal he)

lemma limitMeasure_finite_bound (hB : 0 ≤ B) : limitMeasure Λ hb univ ≤ ENNReal.ofReal B := by
  have : (limitMeasure Λ hb).Regular := RealRMK.regular_rieszMeasure _
  rw [isOpen_univ.measure_eq_iSup_isCompact]
  exact iSup_le (fun K => iSup_le (fun _ => iSup_le (fun hK => limitMeasure_compact_bound Λ hb hB hK)))

end WeakCompact

namespace WeakSobolev
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma gradient_l1_eq {u : E → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    eLpNorm (fderiv ℝ u) 1 μ = ENNReal.ofReal (∫ x, ‖gradient u x‖ ∂μ) := by
  rw [eLpNorm_one_eq_lintegral_enorm (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm
    ((hu.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (hc.fderiv ℝ))]
  simp only [gradient,(InnerProductSpace.toDual ℝ E).symm.norm_map]

lemma smooth_sobolev_two (hd : Module.finrank ℝ E = 2)
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    eLpNorm u 2 μ ≤ (MeasureTheory.eLpNormLESNormFDerivOneConst μ 2 : ℝ≥0∞) *
      ENNReal.ofReal (∫ x, ‖gradient u x‖ ∂μ) := by
  have hp : NNReal.HolderConjugate (Module.finrank ℝ E) 2 := by
    rw [hd]
    exact NNReal.HolderConjugate.two_two
  simpa only [gradient_l1_eq hu hc,ENNReal.coe_ofNat,NNReal.coe_ofNat] using
    MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one μ hu hc hp

lemma gradient_integral_le {u : E → ℝ} {g : E → E}
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (hg : Integrable g μ) :
    (∫ x, ‖gradient u x‖ ∂μ) ≤ (∫ x, ‖g x‖ ∂μ)+(∫ x, ‖gradient u x-g x‖ ∂μ) := by
  have hi : Integrable (gradient u) μ :=
    ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.integrable_comp
      ((hu.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (hc.fderiv ℝ)))
  have he := integral_add hg.norm (hi.sub hg).norm
  simp only [Pi.sub_apply] at he
  rw [← he]
  exact integral_mono hi.norm (hg.norm.add (hi.sub hg).norm) (fun x => by
    simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub (g x) (gradient u x))

/-- The planar Sobolev embedding extended by genuine strong W11 density.
The harmless slack one is used only for finiteness/local convergence. -/
lemma sobolev_two_le (hd : Module.finrank ℝ E = 2)
    {f : E → ℝ} {g : E → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (hw : HasGradient (μ := μ) f g) :
    eLpNorm f 2 μ ≤ (MeasureTheory.eLpNormLESNormFDerivOneConst μ 2 : ℝ≥0∞) *
      ENNReal.ofReal ((∫ x, ‖g x‖ ∂μ)+1) := by
  obtain ⟨u,hu,-,ht,ha⟩ := exists_smooth_sequence hf hg hw
  apply Lp.eLpNorm_le_of_ae_tendsto _ (fun n => (hu n).1.continuous.aestronglyMeasurable)
    hf.aestronglyMeasurable ha
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  apply (smooth_sobolev_two hd ((hu n).1.of_le (by simp)) (hu n).2).trans
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact (gradient_integral_le ((hu n).1.of_le (by simp)) (hu n).2 hg).trans (by linarith)

lemma memLp_two (hd : Module.finrank ℝ E = 2)
    {f : E → ℝ} {g : E → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (hw : HasGradient (μ := μ) f g) : MemLp f 2 μ :=
  (sobolev_two_le hd hf hg hw).trans_lt (by finiteness)

lemma lipschitz_hasGradient {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasGradient (μ := μ) f (gradient f) := by
  intro φ hφ hc v
  obtain ⟨K,hK⟩ := hφ.lipschitzWith_of_hasCompactSupport hc (by simp)
  exact _root_.OAI.LipschitzWith.integral_mul_fderiv_eq_neg hf hK hc v
end WeakSobolev

namespace DiskMaximalTools
lemma rationalMaximal_ae_finite (ν : Measure ℂ) [IsFiniteMeasure ν] :
    ∀ᵐ x, rationalMaximal ν x ≠ ⊤ := by
  rw [ae_iff]
  simp only [not_not]
  change volume {x | rationalMaximal ν x = ⊤} = 0
  apply le_antisymm _ (bot_le)
  have ht := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
    (a := (25:ℝ≥0∞)) (Or.inr (by norm_num))
  have ht' := ENNReal.Tendsto.mul_const ht (b := ν univ) (Or.inr (measure_ne_top _ _))
  simp only [mul_zero,zero_mul] at ht'
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have h := weak_rationalMaximal (ν := ν) (by exact_mod_cast hn : (0:ℝ)<n)
  have hs : {x | rationalMaximal ν x = ⊤} ⊆ {x | ENNReal.ofReal (n:ℝ)<rationalMaximal ν x} := by
    intro x hx
    change ENNReal.ofReal (n:ℝ) < rationalMaximal ν x
    rw [hx]
    exact ENNReal.ofReal_lt_top
  simpa only [ENNReal.ofReal_natCast,div_eq_mul_inv] using (measure_mono hs).trans h

/-- A density measure built from the actual absolute values; a.e. changes of
representative do not change any radius average. -/
def absoluteMeasure (f : ℂ → ℝ) : Measure ℂ := volume.withDensity (fun y => ENNReal.ofReal |f y|)

lemma absoluteMeasure_finite {f : ℂ → ℝ} (hf : Integrable f) : IsFiniteMeasure (absoluteMeasure f) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hf.abs (ae_of_all _ (fun x => abs_nonneg (f x)))]
  exact ENNReal.ofReal_ne_top

lemma absoluteMeasure_congr {f g : ℂ → ℝ} (h : f =ᵐ[volume] g) : absoluteMeasure f = absoluteMeasure g :=
  withDensity_congr_ae (h.mono (fun x hx => by simp only [hx]))

def maximalComplex (f : ℂ → ℝ) (x : ℂ) : ℝ≥0∞ := rationalMaximal (absoluteMeasure f) x
def maximalComplexReal (f : ℂ → ℝ) (x : ℂ) : ℝ := (maximalComplex f x).toReal

lemma memLp_maximalComplexReal_of_measurable {f : ℂ → ℝ} (hm : Measurable f)
    (hf : Integrable f) (hp : MemLp f 2) : MemLp (maximalComplexReal f) 2 := by
  let _ := absoluteMeasure_finite hf
  have hmax : AEStronglyMeasurable (maximalComplexReal f) volume :=
    (measurable_rationalMaximal _).ennreal_toReal.aestronglyMeasurable
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num) hmax]
  let _ : IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal |f x|)) := absoluteMeasure_finite hf
  have h := strong_rationalMaximal hm.abs (fun x => abs_nonneg (f x)) (by norm_num : (1:ℝ)<2)
  have hi := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num) hp.eLpNorm_lt_top
  simp only [ENNReal.toReal_ofNat, ← ofReal_norm,Real.norm_eq_abs,
    ] at hi
  have hi' : ∫⁻ x, ENNReal.ofReal (|f x| ^ (2:ℝ)) < (⊤:ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0:ℝ)≤2)] using hi
  have ht := h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hi')
  simpa only [maximalComplexReal,maximalComplex,absoluteMeasure,ENNReal.toReal_ofNat,
    ← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num : (0:ℝ)≤2)] using ht

lemma memLp_maximalComplexReal {f : ℂ → ℝ} (hf : Integrable f) (hp : MemLp f 2) :
    MemLp (maximalComplexReal f) 2 := by
  let g := hf.aestronglyMeasurable.mk f
  have he : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have h := memLp_maximalComplexReal_of_measurable hm (hf.congr he) (hp.ae_eq he)
  have heM : maximalComplexReal f = maximalComplexReal g := by
    unfold maximalComplexReal maximalComplex
    rw [absoluteMeasure_congr he]
  rwa [heM]

lemma maximalComplex_ae_finite {f : ℂ → ℝ} (hf : Integrable f) :
    ∀ᵐ x, maximalComplex f x ≠ ⊤ := by
  let _ := absoluteMeasure_finite hf
  exact rationalMaximal_ae_finite _

lemma maximalComplex_eq_all_radii (f : ℂ → ℝ) (x : ℂ) :
    maximalComplex f x = ⨆ (r : ℝ) (_ : 0<r), absoluteMeasure f (Metric.ball x r)/volume (Metric.ball x r) := by
  apply le_antisymm
  · apply iSup_le
    intro q
    apply iSup_le
    intro hq
    exact le_iSup_of_le (q:ℝ) (le_iSup_of_le (by exact_mod_cast hq : (0:ℝ)<q) le_rfl)
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr
    exact disk_average_le_rationalMaximal_exact _ x hr
end DiskMaximalTools

namespace WeakSobolev
lemma integral_norm_converges {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} {f : α → F} {u : ℕ → α → F}
    (hf : Integrable f μ) (hu : ∀ n, Integrable (u n) μ)
    (ht : Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖u n x‖ ∂μ) atTop (𝓝 (∫ x, ‖f x‖ ∂μ)) := by
  apply integral_converges_norm hf.norm (fun n => (hu n).norm)
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) _ ht
  intro n
  apply integral_mono ((hu n).norm.sub hf.norm).norm ((hu n).sub hf).norm
  intro x
  simpa only [Real.norm_eq_abs,Pi.sub_apply] using abs_norm_sub_norm_le (u n x) (f x)
end WeakSobolev

namespace SobolevBand
open DiskMoments RadiusEnvelope

def band (f : ℂ → ℝ) (a b : ℝ) := envelope (fun r x => signedAverage f x r) a b

lemma average_abs_le {f : ℂ → ℝ} (hf : Integrable f) {a t : ℝ}
    (ha : 0 < a) (hat : a ≤ t) (x : ℂ) :
    |signedAverage f x t| ≤ (∫ y, ‖f y‖)/(Real.pi*a^2) := by
  have ht : 0 < t := ha.trans_le hat
  have hden : 0 < Real.pi*a^2 := mul_pos Real.pi_pos (sq_pos_of_pos ha)
  rw [signedAverage,abs_div,abs_of_pos (mul_pos Real.pi_pos (sq_pos_of_pos ht))]
  have he : |∫ y in Metric.ball x t, f y| ≤ ∫ y, ‖f y‖ := by
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm f).trans
      (setIntegral_le_integral hf.norm (ae_of_all _ (fun y => norm_nonneg (f y))))
  apply (div_le_div_of_nonneg_right he (by positivity : 0≤Real.pi*t^2)).trans
  exact div_le_div_of_nonneg_left (integral_nonneg (fun y => norm_nonneg (f y))) hden
    (mul_le_mul_of_nonneg_left (sq_le_sq₀ ha.le ht.le |>.mpr hat) Real.pi_pos.le)

lemma average_sub {f h : ℂ → ℝ} (hf : Integrable f) (hh : Integrable h) (x : ℂ) (t : ℝ) :
    signedAverage f x t-signedAverage h x t = signedAverage (f-h) x t := by
  simp only [signedAverage,Pi.sub_apply,integral_sub hf.integrableOn hh.integrableOn,sub_div]

lemma values_bdd {f : ℂ → ℝ} (hf : Integrable f) {a b : ℝ} (ha : 0 < a) (x : ℂ) :
    BddAbove ((fun r => signedAverage f x r) '' Icc a b) := by
  refine ⟨(∫ y, ‖f y‖)/(Real.pi*a^2),?_⟩
  rintro _ ⟨r,hr,rfl⟩
  exact (le_abs_self _).trans (average_abs_le hf ha hr.1 x)

lemma average_le_band {f : ℂ → ℝ} (hf : Integrable f) {a b r : ℝ}
    (ha : 0<a) (hr : r ∈ Icc a b) (x : ℂ) : signedAverage f x r ≤ band f a b x :=
  le_csSup (values_bdd hf ha x) (mem_image_of_mem _ hr)

lemma band_le {f : ℂ → ℝ} {a b M : ℝ} (hab : a ≤ b) (x : ℂ)
    (hM : ∀ r ∈ Icc a b, signedAverage f x r ≤ M) : band f a b x ≤ M := by
  apply csSup_le ((Set.nonempty_Icc.mpr hab).image _)
  rintro _ ⟨r,hr,rfl⟩
  exact hM r hr

lemma band_sub_le {f h : ℂ → ℝ} (hf : Integrable f) (hh : Integrable h)
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (x : ℂ) :
    |band f a b x-band h a b x| ≤ (∫ y, ‖f y-h y‖)/(Real.pi*a^2) := by
  have he (f h : ℂ → ℝ) (hf : Integrable f) (hh : Integrable h) :
      band f a b x ≤ band h a b x+(∫ y, ‖f y-h y‖)/(Real.pi*a^2) := by
    apply band_le hab x
    intro r hr
    have hs := average_abs_le (hf.sub hh) ha hr.1 x
    rw [← average_sub hf hh] at hs
    have hl := average_le_band hh ha hr x
    simp only [Pi.sub_apply] at hs
    linarith [le_abs_self (signedAverage f x r-signedAverage h x r)]
  rw [abs_le]
  constructor
  · have he' := he h f hh hf
    simp only [norm_sub_rev (h _) (f _)] at he'
    linarith
  · linarith [he f h hf hh]

lemma smooth_average_lipschitz {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {a t : ℝ} (ha : 0<a) (hat : a≤t) :
    LipschitzWith (⟨(∫ y, ‖gradient f y‖)/(Real.pi*a^2),by positivity⟩ : ℝ≥0) (fun x => signedAverage f x t) := by
  obtain ⟨L,hL⟩ := hf.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  have hD := fun y => norm_fderiv_le_of_lipschitz ℝ hL (x₀ := y)
  have hi : Integrable (gradient f) := (continuous_gradient hf).integrable_of_hasCompactSupport (gradient_hasCompactSupport hc)
  have ht := ha.trans_le hat
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hasFDerivAt_signedAverage hf hD x ht).differentiableAt)
  intro x
  change ‖fderiv ℝ (fun x => signedAverage f x t) x‖ ≤ _
  rw [← (InnerProductSpace.toDual ℝ ℂ).symm.norm_map]
  change ‖gradient (fun x => signedAverage f x t) x‖ ≤ _
  rw [gradient_signedAverage hf hD x ht,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(Real.pi*t^2)⁻¹)]
  have he : ‖∫ y in Metric.ball x t, gradient f y‖ ≤ ∫ y, ‖gradient f y‖ :=
    (norm_integral_le_integral_norm _).trans (setIntegral_le_integral hi.norm (ae_of_all _ (fun y => norm_nonneg _)))
  rw [← div_eq_inv_mul]
  exact (div_le_div_of_nonneg_right he (by positivity)).trans
    (div_le_div_of_nonneg_left (integral_nonneg (fun y => norm_nonneg _)) (by positivity)
      (mul_le_mul_of_nonneg_left (sq_le_sq₀ ha.le ht.le |>.mpr hat) Real.pi_pos.le))

lemma smooth_band_lipschitz {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    LipschitzWith (⟨(∫ y, ‖gradient f y‖)/(Real.pi*a^2),by positivity⟩ : ℝ≥0) (band f a b) :=
  RadiusEnvelope.lipschitz hab (fun x => signedAverage_radius_continuousOn hf x ha)
    (fun _ hr => smooth_average_lipschitz hf hc ha hr.1)

lemma band_converges {f : ℂ → ℝ} {u : ℕ → ℂ → ℝ} (hf : Integrable f) (hu : ∀ n, Integrable (u n))
    (ht : Tendsto (fun n => ∫ x, ‖u n x-f x‖) atTop (𝓝 0))
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (x : ℂ) :
    Tendsto (fun n => band (u n) a b x) atTop (𝓝 (band f a b x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => by simpa only [Real.norm_eq_abs] using band_sub_le (hu n) hf ha hab x)
  simpa only [zero_div,Real.norm_eq_abs] using ht.div_const (Real.pi*a^2)

lemma band_lipschitz {f : ℂ → ℝ} {g : ℂ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hw : WeakSobolev.HasGradient (μ := volume) f g) {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    LipschitzWith (⟨(∫ y, ‖g y‖)/(Real.pi*a^2),by positivity⟩ : ℝ≥0) (band f a b) := by
  obtain ⟨u,hu,huf,hvg,-⟩ := WeakSobolev.exists_smooth_sequence hf hg hw
  have hi (n) : Integrable (u n) := (hu n).1.continuous.integrable_of_hasCompactSupport (hu n).2
  have hgi (n) : Integrable (gradient (u n)) :=
    (continuous_gradient ((hu n).1.of_le (by simp))).integrable_of_hasCompactSupport (gradient_hasCompactSupport (hu n).2)
  have hgt := WeakSobolev.integral_norm_converges hg hgi hvg
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto_of_tendsto ((band_converges hf hi huf ha hab x).dist (band_converges hf hi huf ha hab y))
    ((hgt.div_const (Real.pi*a^2)).mul_const (dist x y))
  exact Eventually.of_forall (fun n => (smooth_band_lipschitz ((hu n).1.of_le (by simp)) (hu n).2 ha hab).dist_le_mul x y)
end SobolevBand

namespace WeakCompact
open CompactlySupported CompactlySupportedContinuousMap
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] {μ : Measure X}

omit [T2Space X] [LocallyCompactSpace X] in
lemma density_test_integrable {w : X → ℝ} (hw : Integrable w μ) (φ : C_c(X,ℝ)) :
    Integrable (fun x => w x*φ x) μ := by
  apply hw.mul_bdd φ.continuous.aestronglyMeasurable
  exact ae_of_all _ (fun x => φ.toBoundedContinuousFunction.norm_coe_le_norm x)

def densityPositive {w : X → ℝ} (hw : Integrable w μ) (h0 : ∀ᵐ x ∂μ, 0≤w x) : C_c(X,ℝ) →ₚ[ℝ] ℝ where
  toFun φ := ∫ x, w x*φ x ∂μ
  map_add' φ ψ := by
    simp only [CompactlySupportedContinuousMap.coe_add,Pi.add_apply,mul_add]
    exact integral_add (density_test_integrable hw φ) (density_test_integrable hw ψ)
  map_smul' c φ := by
    simp only [CompactlySupportedContinuousMap.coe_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp_rw [← mul_assoc,mul_comm (w _) c,mul_assoc]
    exact integral_const_mul c _
  monotone' := by
    intro φ ψ hφψ
    apply integral_mono_ae (density_test_integrable hw φ) (density_test_integrable hw ψ)
    filter_upwards [h0] with x hx
    exact mul_le_mul_of_nonneg_left (hφψ x) hx

omit [T2Space X] [LocallyCompactSpace X] in
lemma densityPositive_bound {w : X → ℝ} (hw : Integrable w μ) (h0 : ∀ᵐ x ∂μ, 0≤w x) (φ : C_c(X,ℝ)) :
    |densityPositive hw h0 φ| ≤ (∫ x,w x ∂μ)*‖φ.toBoundedContinuousFunction‖ := by
  apply (show |∫ x,w x*φ x ∂μ| ≤ ∫ x,‖w x*φ x‖ ∂μ by exact norm_integral_le_integral_norm (fun x => w x*φ x)).trans
  rw [← integral_mul_const]
  apply integral_mono_ae (density_test_integrable hw φ).norm (hw.mul_const _)
  filter_upwards [h0] with x hx
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hx]
  exact mul_le_mul_of_nonneg_left (φ.toBoundedContinuousFunction.norm_coe_le_norm x) hx

omit [T2Space X] [LocallyCompactSpace X] in
lemma densityPositive_norm_bound {w : X → ℝ} (hw : Integrable w μ) (h0 : ∀ᵐ x ∂μ, 0≤w x)
    {B : ℝ} (hB : (∫ x,w x ∂μ) ≤ B) (φ : C_c(X,ℝ)) :
    |densityPositive hw h0 φ| ≤ B*‖φ.toBoundedContinuousFunction‖ :=
  (densityPositive_bound hw h0 φ).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))

omit [T2Space X] [LocallyCompactSpace X] in
lemma density_test_le_set {w : X → ℝ} (hw : Integrable w μ) (h0 : ∀ᵐ x ∂μ, 0≤w x)
    (φ : C_c(X,ℝ)) {O : Set X} (hO : MeasurableSet O) (hs : tsupport φ ⊆ O)
    (hφ : ∀ x, φ x≤1) : (∫ x,w x*φ x ∂μ) ≤ ∫ x in O,w x ∂μ := by
  rw [← integral_indicator hO]
  apply integral_mono_ae (density_test_integrable hw φ) (hw.indicator hO)
  filter_upwards [h0] with x hx
  by_cases hxo : x∈O
  · rw [indicator_of_mem hxo]
    exact mul_le_of_le_one_right hx (hφ x)
  · rw [indicator_of_notMem hxo,image_eq_zero_of_notMem_tsupport (fun h => hxo (hs h)),mul_zero]

variable (w : ℕ → X → ℝ) (hw : ∀ n, Integrable (w n) μ) (h0 : ∀ n, ∀ᵐ x ∂μ, 0≤w n x)
  {B : ℝ} (hb : ∀ n, (∫ x,w n x ∂μ) ≤ B)

def densityLimit : Measure X := limitMeasure (fun n => densityPositive (hw n) (h0 n))
  (fun n φ => densityPositive_norm_bound (hw n) (h0 n) (hb n) φ)

lemma densityLimit_integral (φ : C_c(X,ℝ)) :
    Tendsto (fun n => ∫ x,w n x*φ x ∂μ) (hyperfilter ℕ) (𝓝 (∫ x,φ x ∂densityLimit w hw h0 hb)) :=
  integral_limitMeasure _ _ φ

lemma densityLimit_mass (hB : 0≤B) : densityLimit w hw h0 hb univ ≤ ENNReal.ofReal B :=
  limitMeasure_finite_bound _ _ hB

lemma densityLimit_regular : (densityLimit w hw h0 hb).Regular := RealRMK.regular_rieszMeasure _
lemma densityLimit_finite (hB : 0≤B) : IsFiniteMeasure (densityLimit w hw h0 hb) :=
  ⟨(densityLimit_mass w hw h0 hb hB).trans_lt ENNReal.ofReal_lt_top⟩

/-- The local lower-semicontinuity estimate needed for null-set localization.
Only eventual bounds are required, so large-radius splitting may start late. -/
lemma densityLimit_compact_bound {D : ℝ} {K O : Set X} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) (hD : ∀ᶠ n in atTop, (∫ x in O,w n x ∂μ) ≤ D) :
    densityLimit w hw h0 hb K ≤ ENNReal.ofReal D := by
  obtain ⟨φ,hφ1,hφc,hφs,hφ⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO
  let φ' : C_c(X,ℝ) := ⟨φ,hφc⟩
  have hm := RealRMK.rieszMeasure_le_of_eq_one
    (limitPositive (fun n => densityPositive (hw n) (h0 n))
      (fun n ψ => densityPositive_norm_bound (hw n) (h0 n) (hb n) ψ))
    (f := φ') (fun x => (hφ x).1) hK hφ1
  have he : limitPositive (fun n => densityPositive (hw n) (h0 n))
      (fun n ψ => densityPositive_norm_bound (hw n) (h0 n) (hb n) ψ) φ' ≤ D := by
    apply le_of_tendsto (limit_tendsto (fun n => densityPositive (hw n) (h0 n))
      (fun n ψ => densityPositive_norm_bound (hw n) (h0 n) (hb n) ψ) φ')
    filter_upwards [Nat.hyperfilter_le_atTop hD] with n hn
    exact (density_test_le_set (hw n) (h0 n) φ' hO.measurableSet hφs (fun x => (hφ x).2)).trans hn
  exact hm.trans (ENNReal.ofReal_le_ofReal he)
end WeakCompact

namespace WeakCompact
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] {μ : Measure X}
variable (w : ℕ → X → ℝ) (hw : ∀ n, Integrable (w n) μ) (h0 : ∀ n, ∀ᵐ x ∂μ, 0≤w n x)
  {B : ℝ} (hb : ∀ n, (∫ x,w n x ∂μ) ≤ B)

lemma densityLimit_sharp_mass {D : ℝ} {a : ℕ → ℝ}
    (ha : ∀ n, (∫ x,w n x ∂μ) ≤ a n) (ht : Tendsto a atTop (𝓝 D)) :
    densityLimit w hw h0 hb Set.univ ≤ ENNReal.ofReal D := by
  have := densityLimit_regular w hw h0 hb
  rw [isOpen_univ.measure_eq_iSup_isCompact]
  apply iSup_le
  intro K
  apply iSup_le
  intro _
  apply iSup_le
  intro hK
  have he (ε : ℝ) (hε : 0<ε) : densityLimit w hw h0 hb K ≤ ENNReal.ofReal (D+ε) := by
    apply densityLimit_compact_bound w hw h0 hb hK isOpen_univ (subset_univ K)
    filter_upwards [ht.eventually (gt_mem_nhds (by linarith : D<D+ε))] with n hn
    simpa only [Measure.restrict_univ] using (ha n).trans hn.le
  apply le_of_tendsto_of_tendsto (tendsto_const_nhds (x := densityLimit w hw h0 hb K))
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (show Tendsto (fun n : ℕ => D+1/((n:ℝ)+1)) atTop (𝓝 D) by
        simpa only [add_zero] using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))
  exact Eventually.of_forall (fun n => he _ (by positivity))

omit [T2Space X] [BorelSpace X] [LocallyCompactSpace X] in
lemma absolutelyContinuous_of_compact_null {ν : Measure X} [ν.InnerRegular]
    (h : ∀ K : Set X, IsCompact K → μ K=0 → ν K=0) : ν ≪ μ := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hμ
  rw [hs.measure_eq_iSup_isCompact]
  apply le_antisymm _ bot_le
  apply iSup_le
  intro K
  apply iSup_le
  intro hKs
  apply iSup_le
  intro hK
  exact (h K hK (measure_mono_null hKs hμ)).le
end WeakCompact

namespace SobolevBand
open DiskMoments DiskMaximalTools

def low (n : ℕ) : ℝ := ((2:ℝ)^n)⁻¹
def high (n : ℕ) : ℝ := 2*(2:ℝ)^n
lemma low_pos (n : ℕ) : 0<low n := by unfold low; positivity
lemma high_pos (n : ℕ) : 0<high n := by unfold high; positivity
lemma low_le_high (n : ℕ) : low n ≤ high n := by
  have hp : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
  unfold low high
  have hi : ((2:ℝ)^n)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hp
  linarith
lemma low_antitone : Antitone low := by
  intro n m hnm
  exact inv_anti₀ (by positivity : (0:ℝ)<2^n) (pow_le_pow_right₀ (by norm_num) hnm)
lemma high_monotone : Monotone high := by
  intro n m hnm
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hnm) (by norm_num)
lemma low_tendsto : Tendsto low atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((2:ℝ)^n)⁻¹) atTop (𝓝 0)
  simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤2⁻¹) (by norm_num : (2⁻¹:ℝ)<1)
lemma high_tendsto : Tendsto high atTop atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).const_mul_atTop (by norm_num)
lemma eventually_mem_band {r : ℝ} (hr : 0<r) : ∀ᶠ n in atTop, r∈Icc (low n) (high n) := by
  filter_upwards [low_tendsto.eventually (gt_mem_nhds hr),high_tendsto.eventually (eventually_ge_atTop r)] with n hn hn'
  exact ⟨hn.le,hn'⟩

lemma absolute_average_eq {f : ℂ → ℝ} (hf : Integrable f) (x : ℂ) {r : ℝ} (hr : 0<r) :
    absoluteMeasure f (Metric.ball x r)/volume (Metric.ball x r) =
      ENNReal.ofReal (signedAverage (fun y => |f y|) x r) := by
  rw [absoluteMeasure,withDensity_apply _ measurableSet_ball,volume_disk_real x hr.le,signedAverage,
    ENNReal.ofReal_div_of_pos (mul_pos Real.pi_pos (sq_pos_of_pos hr)),
    ofReal_integral_eq_lintegral_ofReal hf.abs.integrableOn (ae_of_all _ (fun y => abs_nonneg (f y)))]

lemma abs_average_nonneg (f : ℂ → ℝ) (x : ℂ) {r : ℝ} (hr : 0<r) :
    0 ≤ signedAverage (fun y => |f y|) x r := by
  unfold signedAverage
  exact div_nonneg (integral_nonneg (fun _ => abs_nonneg _)) (by positivity)

lemma abs_band_nonneg {f : ℂ → ℝ} (hf : Integrable f) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) (x : ℂ) : 0 ≤ band (fun y => |f y|) a b x :=
  (abs_average_nonneg f x ha).trans (average_le_band hf.abs ha ⟨le_rfl,hab⟩ x)

lemma abs_band_le_maximal {f : ℂ → ℝ} (hf : Integrable f) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) {x : ℂ} (hx : maximalComplex f x ≠ ⊤) :
    band (fun y => |f y|) a b x ≤ maximalComplexReal f x := by
  apply band_le hab x
  intro r hr
  apply (ENNReal.ofReal_le_iff_le_toReal hx).mp
  rw [← absolute_average_eq hf x (ha.trans_le hr.1)]
  exact disk_average_le_rationalMaximal_exact _ x (ha.trans_le hr.1)

lemma band_mono_interval {f : ℂ → ℝ} (hf : Integrable f) {a b c d : ℝ}
    (ha : 0<a) (hac : a≤c) (hcd : c≤d) (hdb : d≤b) (x : ℂ) :
    band f c d x ≤ band f a b x := by
  apply band_le hcd x
  intro r hr
  exact average_le_band hf ha ⟨hac.trans hr.1,hr.2.trans hdb⟩ x

lemma diagonal_monotone {f : ℂ → ℝ} (hf : Integrable f) (x : ℂ) :
    Monotone (fun n => band f (low n) (high n) x) := by
  intro n m hnm
  exact band_mono_interval hf (low_pos m) (low_antitone hnm) (low_le_high n) (high_monotone hnm) x

lemma diagonal_tendsto {f : ℂ → ℝ} (hf : Integrable f) {x : ℂ} (hx : maximalComplex f x≠⊤) :
    Tendsto (fun n => band (fun y => |f y|) (low n) (high n) x) atTop (𝓝 (maximalComplexReal f x)) := by
  let v := fun n => band (fun y => |f y|) (low n) (high n) x
  have hb : BddAbove (range v) := ⟨maximalComplexReal f x,by
    rintro _ ⟨n,rfl⟩; exact abs_band_le_maximal hf (low_pos n) (low_le_high n) hx⟩
  have hs0 : 0≤⨆ n,v n := (abs_band_nonneg hf (low_pos 0) (low_le_high 0) x).trans (le_ciSup hb 0)
  have hs : (⨆ n,v n) = maximalComplexReal f x := by
    apply le_antisymm
    · apply ciSup_le
      intro n
      exact abs_band_le_maximal hf (low_pos n) (low_le_high n) hx
    · have he : maximalComplex f x ≤ ENNReal.ofReal (⨆ n,v n) := by
        rw [maximalComplex_eq_all_radii]
        apply iSup_le
        intro r
        apply iSup_le
        intro hr
        obtain ⟨n,hn⟩ := (eventually_mem_band hr).exists
        rw [absolute_average_eq hf x hr]
        exact ENNReal.ofReal_le_ofReal ((average_le_band hf.abs (low_pos n) hn x).trans (le_ciSup hb n))
      simpa only [maximalComplexReal,ENNReal.toReal_ofReal hs0] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  rw [← hs]
  exact tendsto_atTop_ciSup (diagonal_monotone hf.abs x) hb

lemma locallyIntegrable_maximal {f : ℂ → ℝ} {g : ℂ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hw : WeakSobolev.HasGradient (μ := volume) f g) :
    LocallyIntegrable (maximalComplexReal f) :=
  (memLp_maximalComplexReal hf (WeakSobolev.memLp_two Complex.finrank_real_complex hf hg hw)).locallyIntegrable (by norm_num)

lemma diagonal_local_L1 {f : ℂ → ℝ} {g : ℂ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hw : WeakSobolev.HasGradient (μ := volume) f g)
    {K : Set ℂ} (hK : IsCompact K) :
    Tendsto (fun n => ∫ x in K, ‖band (fun y => |f y|) (low n) (high n) x-maximalComplexReal f x‖) atTop (𝓝 0) := by
  let _ := absoluteMeasure_finite hf
  have hg' := (WeakSobolev.abs_gradient_bound hf hg).1
  have hw' := hw.abs hf hg
  have hL n := band_lipschitz hf.abs hg' hw' (low_pos n) (low_le_high n)
  have hM := locallyIntegrable_maximal hf hg hw
  have ht := tendsto_integral_of_dominated_convergence (f := fun _ : ℂ => (0:ℝ))
    (fun x => 2*maximalComplexReal f x)
    (fun n => (((hL n).continuous.aestronglyMeasurable).sub ((measurable_rationalMaximal (absoluteMeasure f)).ennreal_toReal.aestronglyMeasurable)).norm.restrict)
    ((hM.integrableOn_isCompact hK).const_mul 2)
    (fun n => ?_) (?_)
  · simpa only [integral_zero,Pi.sub_apply,maximalComplexReal,maximalComplex] using ht
  · filter_upwards [ae_restrict_of_ae (maximalComplex_ae_finite hf)] with x hx
    have h0 := abs_band_nonneg hf (low_pos n) (low_le_high n) x
    have h1 := abs_band_le_maximal hf (low_pos n) (low_le_high n) hx
    change ‖‖band (fun y => |f y|) (low n) (high n) x-maximalComplexReal f x‖‖ ≤ _
    rw [Real.norm_of_nonneg (norm_nonneg _),Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr h1)]
    have h2 : 0 ≤ maximalComplexReal f x := ENNReal.toReal_nonneg
    linarith
  · filter_upwards [ae_restrict_of_ae (maximalComplex_ae_finite hf)] with x hx
    simpa only [sub_self,norm_zero,Pi.sub_apply,maximalComplexReal,maximalComplex] using ((diagonal_tendsto hf hx).sub (tendsto_const_nhds (x := maximalComplexReal f x))).norm
end SobolevBand

namespace SobolevBand
open DiskMoments RadiusEnvelope SignedRuns GeometricFilter DyadicHats ActualLabels

lemma geometric_band_eq (f : ℂ → ℝ) (a : ℝ) (m : ℕ) :
    runEnvelope f (geometricRadii a m) 0 m = band f a (2*((2:ℝ)^m*a)) := by
  unfold runEnvelope band
  rw [geometricRadii_eq a (le_refl m),geometricRadii_eq a (Nat.zero_le m)]
  simp only [Nat.sub_self,Nat.sub_zero,scale,pow_zero,one_mul]

lemma smooth_band_integrable_gradient {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    Integrable (gradient (band f a b)) :=
  _root_.OAI.LipschitzWith.integrable_gradient (smooth_band_lipschitz hf hc ha hab) (run_envelope_hasCompactSupport hf hc ha hab)

lemma smooth_dyadic_bound : ∃ C : ℝ, 0<C ∧ ∀ {f : ℂ → ℝ}, ContDiff ℝ 1 f →
    HasCompactSupport f → ∀ {a : ℝ}, 0<a → ∀ m : ℕ,
    (∫ x,‖gradient (band f a (2*((2:ℝ)^m*a))) x‖) ≤ C*(∫ x,‖gradient f x‖) := by
  obtain ⟨C,hC,he⟩ := smooth_compact_dyadic_band
  refine ⟨C,hC,?_⟩
  intro f hf hc a ha m
  simpa only [geometric_band_eq] using he hf hc ha m

lemma band_ae_touching {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    ∀ᵐ x, ∀ r ∈ Icc a b, band f a b x=signedAverage f x r →
      gradient (band f a b) x=gradient (fun y => signedAverage f y r) x := by
  obtain ⟨L,hL⟩ := hf.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  filter_upwards [(smooth_band_lipschitz hf hc ha hab).ae_differentiableAt] with x hx
  intro r hr he
  have hd := (hasFDerivAt_signedAverage hf (fun y => norm_fderiv_le_of_lipschitz ℝ hL (x₀ := y)) x (ha.trans_le hr.1)).differentiableAt
  exact congrArg (InnerProductSpace.toDual ℝ ℂ).symm
    (fderiv_touching hr (fun y => signedAverage_radius_continuousOn hf y ha) he hx hd)

/-- Quantitative large-radius truncation; small radii are the only term needing
localization. Differentiable touching avoids any unproved max-chain rule. -/
lemma split_gradient {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {a t b : ℝ} (ha : 0<a) (hat : a≤t) (htb : t≤b) :
    ∀ᵐ x, ‖gradient (band f a b) x‖ ≤ ‖gradient (band f a t) x‖+
      (∫ y,‖gradient f y‖)/(Real.pi*t^2) := by
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  filter_upwards [band_ae_touching hf hc ha (hat.trans htb),band_ae_touching hf hc ha hat] with x hx hx'
  obtain ⟨r,hr,he,hm⟩ := attains (u := fun r x => signedAverage f x r) (hat.trans htb) x (signedAverage_radius_continuousOn hf x ha)
  have htouch := hx r hr he
  by_cases hrt : r≤t
  · have hs : band f a t x=signedAverage f x r := by
      apply le_antisymm
      · apply band_le hat x
        intro s hs
        exact hm s ⟨hs.1,hs.2.trans htb⟩
      · exact average_le_band hfi ha ⟨hr.1,hrt⟩ x
    rw [htouch,← hx' r ⟨hr.1,hrt⟩ hs]
    exact le_add_of_nonneg_right (by positivity)
  · rw [htouch]
    have hnorm := norm_fderiv_le_of_lipschitz ℝ (smooth_average_lipschitz hf hc (ha.trans_le hat) (le_of_not_ge hrt)) (x₀ := x)
    rw [← WeakSobolev.norm_gradient_fderiv] at hnorm
    exact hnorm.trans (le_add_of_nonneg_left (norm_nonneg _))
end SobolevBand

end

end OAI
