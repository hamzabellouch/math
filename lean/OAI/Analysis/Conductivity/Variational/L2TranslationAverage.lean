import Mathlib
import OAI.Analysis.Conductivity.Variational.RadialWeylScale

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

abbrev WholeL2 := Lp ℝ 2 (volume : Measure R3)

def translateL2 (y : R3) (f : WholeL2) : WholeL2 :=
  Lp.compMeasurePreserving (fun x => x-y) (measurePreserving_sub_right volume y) f

lemma translateL2_ae (y : R3) (f : WholeL2) :
    (translateL2 y f : R3 → ℝ) =ᵐ[volume] fun x => f (x-y) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma translateL2_norm (y : R3) (f : WholeL2) : ‖translateL2 y f‖=‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

lemma translateL2_zero (f : WholeL2) : translateL2 0 f=f := by
  apply Lp.ext
  filter_upwards [translateL2_ae 0 f] with x hx
  simpa using hx

lemma continuous_translateL2 (f : WholeL2) : Continuous (fun y => translateL2 y f) := by
  let T : C(R3,C(R3,R3)) := (⟨fun z : R3×R3 => z.2-z.1,continuous_snd.sub continuous_fst⟩ : C(R3×R3,R3)).curry
  exact continuous_const.compMeasurePreservingLp T.continuous
    (fun y => measurePreserving_sub_right volume y) (by norm_num)

lemma wholeL2_norm_sq (f : WholeL2) : ‖f‖^2=∫ x, f x^2 := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

lemma translate_difference_sq (f : WholeL2) (y : R3) :
    (∫ x, (f (x-y)-f x)^2)=‖translateL2 y f-f‖^2 := by
  rw [wholeL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (translateL2 y f) f,translateL2_ae y f] with x hx hy
  simp only [hx,Pi.sub_apply,hy]

lemma whole_translation_memLp {μ : Measure R3} [IsProbabilityMeasure μ] (f : WholeL2) :
    MemLp (fun z : R3×R3 => f (z.2-z.1)) 2 (μ.prod volume) := by
  have hm : StronglyMeasurable (fun z : R3×R3 => f (z.2-z.1)) :=
    (Lp.stronglyMeasurable f).comp_measurable (measurable_snd.sub measurable_fst)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hm.pow 2).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun y => ((Lp.memLp f).comp_measurePreserving (measurePreserving_sub_right volume y)).integrable_sq)
  · have he (y : R3) : (∫ x, ‖f (x-y)^2‖)=‖f‖^2 := by
      rw [←translateL2_norm y f,wholeL2_norm_sq]
      apply integral_congr_ae
      filter_upwards [translateL2_ae y f] with x hx
      simp [hx]
    change Integrable (fun y => ∫ x, ‖f (x-y)^2‖) μ
    simp_rw [he]
    exact integrable_const _

lemma whole_difference_memLp {μ : Measure R3} [IsProbabilityMeasure μ] (f : WholeL2) :
    MemLp (fun z : R3×R3 => f (z.2-z.1)-f z.2) 2 (μ.prod volume) := by
  have hm : StronglyMeasurable (fun z : R3×R3 => f z.2) :=
    (Lp.stronglyMeasurable f).comp_measurable measurable_snd
  have hf : MemLp (fun z : R3×R3 => f z.2) 2 (μ.prod volume) := by
    apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
    apply (integrable_prod_iff (hm.pow 2).aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ (fun _ => (Lp.memLp f).integrable_sq)
    · change Integrable (fun _ : R3 => ∫ y, ‖f y^2‖) μ
      exact integrable_const _
  exact (whole_translation_memLp f).sub hf

theorem translation_average_sq_le {μ : Measure R3} [IsProbabilityMeasure μ]
    (f : WholeL2) {ε : ℝ}
    (hε : ∀ᵐ y ∂μ, ‖translateL2 y f-f‖^2≤ε) :
    MemLp (fun x => ∫ y, (f (x-y)-f x) ∂μ) 2 volume ∧
    (∫ x, (∫ y, (f (x-y)-f x) ∂μ)^2) ≤ ε := by
  obtain ⟨hm,hbound⟩ := memLp_probability_average (whole_difference_memLp (μ := μ) f)
  refine ⟨hm,hbound.trans ?_⟩
  rw [integral_prod _ (whole_difference_memLp (μ := μ) f).integrable_sq]
  have hi := (whole_difference_memLp (μ := μ) f).integrable_sq.integral_prod_left
  calc
    _ ≤ ∫ _ : R3, ε ∂μ := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [hε] with y hy
      exact (translate_difference_sq f y).le.trans hy
    _ = ε := by simp

lemma small_translation_radius (f : WholeL2) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ y : R3, ‖y‖<δ → ‖translateL2 y f-f‖^2<ε := by
  have hc : Continuous (fun y => ‖translateL2 y f-f‖^2) :=
    ((continuous_translateL2 f).sub continuous_const).norm.pow 2
  have he : (fun y => ‖translateL2 y f-f‖^2) 0=0 := by simp [translateL2_zero]
  have hn : ∀ᶠ y in 𝓝 (0:R3), ‖translateL2 y f-f‖^2<ε :=
    hc.continuousAt.eventually (gt_mem_nhds (by simpa [he] using hε))
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp hn
  exact ⟨δ,hδ,fun y hy => hd (by simpa [dist_zero_right] using hy)⟩

open Set MeasureTheory Filter Topology
open scoped Convolution

def radialProbability (s : ℝ) : Measure WeylSpace :=
  volume.withDensity (fun x => ENNReal.ofReal (radialEta radialProfile s x))

lemma radialProbability_probability {s : ℝ} (hs : 0<s) : IsProbabilityMeasure (radialProbability s) where
  measure_univ := by
    rw [radialProbability,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ←ofReal_integral_eq_lintegral_ofReal
        ((radialEta_smooth s).continuous.integrable_of_hasCompactSupport (radialEta_compact hs))
        (ae_of_all _ (radialEta_nonneg hs)),radialEta_integral hs]
    simp

lemma radialProbability_integral {s : ℝ} (hs : 0<s) (f : WeylSpace → ℝ) :
    (∫ y, f y ∂radialProbability s)=∫ y, radialEta radialProfile s y*f y := by
  rw [radialProbability,integral_withDensity_eq_integral_toReal_smul
    (radialEta_smooth s).continuous.measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (radialEta_nonneg hs _),smul_eq_mul]

lemma radialProbability_ball {s : ℝ} (hs : 0<s) :
    ∀ᵐ y ∂radialProbability s, ‖y‖<s := by
  rw [radialProbability,ae_withDensity_iff (radialEta_smooth s).continuous.measurable.ennreal_ofReal]
  filter_upwards with y hy
  by_contra hn
  have he := radialEta_zero hs (not_lt.mp hn)
  exact hy (by rw [he]; simp)

lemma radialMollify_eq_average {s : ℝ} (hs : 0<s) (f : WeylSpace → ℝ) (x : WeylSpace) :
    radialMollify f s x=∫ y, f (x-y) ∂radialProbability s := by
  rw [radialProbability_integral hs,radialMollify,convolution_eq_swap]
  congr 1
  ext y
  simp [mul_comm]

lemma radialMollify_sub {s : ℝ} (hs : 0<s) (f : WholeL2) (x : WeylSpace) :
    radialMollify f s x-f x=∫ y, (f (x-y)-f x) ∂radialProbability s := by
  rw [radialProbability_integral hs]
  simp_rw [mul_sub]
  have hi : Integrable (fun y => radialEta radialProfile s y*f (x-y)) :=
    (radialEta_compact hs).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (radialEta_smooth s).continuous ((Lp.memLp f).locallyIntegrable (by norm_num)) x
  rw [integral_sub hi (((radialEta_smooth s).continuous.integrable_of_hasCompactSupport
    (radialEta_compact hs)).mul_const _),integral_mul_const,radialEta_integral hs,one_mul]
  rw [radialMollify_eq_average hs,radialProbability_integral hs]

lemma radialMollify_memLp {s : ℝ} (hs : 0<s) (f : WholeL2) :
    MemLp (radialMollify f s) 2 volume := by
  let := radialProbability_probability hs
  obtain ⟨hm,_⟩ := memLp_probability_average (whole_translation_memLp (μ := radialProbability s) f)
  exact MemLp.ae_eq (ae_of_all _ (fun x => (radialMollify_eq_average hs f x).symm)) hm

theorem radialMollify_approx (f : WholeL2) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ s : ℝ, 0<s → s≤δ →
      (∫ x, (radialMollify f s x-f x)^2) ≤ ε := by
  obtain ⟨δ,hδ,hd⟩ := small_translation_radius f hε
  refine ⟨δ,hδ,fun s hs hsd => ?_⟩
  let := radialProbability_probability hs
  obtain ⟨_,he⟩ := translation_average_sq_le (μ := radialProbability s) f
    (show ∀ᵐ y ∂radialProbability s, ‖translateL2 y f-f‖^2≤ε from by
      filter_upwards [radialProbability_ball hs] with y hy
      exact (hd y (hy.trans_le hsd)).le)
  simpa only [radialMollify_sub hs] using he

end ScalarConductivity

end

end OAI
