import Mathlib
import OAI.Probability.SKSupport.Foundations.GradientAbs
import OAI.Probability.SKSupport.Diffusion.ProgressiveBrownian
import OAI.Probability.SKSupport.Diffusion.PicardUniqueness
import OAI.Probability.SKSupport.Regularity.JointRegularity

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat

def stripClamp (T t : ℝ) : ℝ := max 0 (min T t)

lemma stripClamp_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : stripClamp T t ∈ Icc (0:ℝ) T :=
  ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩

lemma stripClamp_eq {T t : ℝ} (ht : t ∈ Icc (0:ℝ) T) : stripClamp T t = t := by
  simp only [stripClamp,min_eq_right ht.2,max_eq_right ht.1]

lemma continuous_stripClamp (T : ℝ) : Continuous (stripClamp T) :=
  continuous_const.max (continuous_const.min continuous_id)

variable {Ω : Type*} [MeasurableSpace Ω]

def compactGradient (W : BrownianSystem Ω) (γ : OrderParameter) (T : ℝ) (t x : ℝ) : ℝ :=
  gradient W γ (stripClamp T t) x

def compactCoeff (γ : OrderParameter) (T t : ℝ) : ℝ := extend γ.val (stripClamp T t)

def compactDrift (W : BrownianSystem Ω) (γ : OrderParameter) (T t x : ℝ) : ℝ :=
  compactCoeff γ T t*compactGradient W γ T t x

lemma compactGradient_continuous (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Continuous (fun p : ℝ × ℝ => compactGradient W γ T p.1 p.2) := by
  have hc := value_derivative_continuousOn W γ hT0 hT1 1
  simp only [iteratedDeriv_one] at hc
  apply continuousOn_univ.mp
  exact hc.comp (((continuous_stripClamp T).comp continuous_fst).prodMk continuous_snd).continuousOn
    (fun p _ => ⟨stripClamp_mem hT0 p.1,mem_univ _⟩)

lemma compactGradient_bound (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    |compactGradient W γ T t x| ≤ 1 :=
  gradient_abs_le_one W γ _ x ((stripClamp_mem hT0 t).2.trans hT1.le)

lemma compactCoeff_measurable (γ : OrderParameter) (T : ℝ) : Measurable (compactCoeff γ T) :=
  γ.measurable_extend.comp (continuous_stripClamp T).measurable

lemma compactCoeff_bounds (γ : OrderParameter) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t : ℝ) :
    0 ≤ compactCoeff γ T t ∧ compactCoeff γ T t ≤ γ.val ⟨T,⟨hT0,hT1⟩⟩ := by
  have ht := stripClamp_mem hT0 t
  have hm : stripClamp T t ∈ Ico (0:ℝ) 1 := ⟨ht.1,ht.2.trans_lt hT1⟩
  simp only [compactCoeff,extend,dite_eq_left hm]
  exact ⟨γ.nonneg _,γ.monotone ht.2⟩

lemma compactDrift_measurable (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Measurable (fun p : ℝ × ℝ => compactDrift W γ T p.1 p.2) :=
  ((compactCoeff_measurable γ T).comp measurable_fst).mul
    (compactGradient_continuous W γ hT0 hT1).measurable

lemma compactDrift_bound (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    |compactDrift W γ T t x| ≤ γ.val ⟨T,⟨hT0,hT1⟩⟩ := by
  have hc := compactCoeff_bounds γ hT0 hT1 t
  rw [compactDrift,abs_mul,abs_of_nonneg hc.1]
  exact (mul_le_of_le_one_right hc.1 (compactGradient_bound W γ hT0 hT1 t x)).trans hc.2

lemma compactGradient_lipschitz (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∃ L : ℝ≥0, ∀ t, LipschitzWith L (compactGradient W γ T t) := by
  obtain ⟨C,hC,hb⟩ := value_uniform_derivative_bounds W γ hT0 hT1 1
  refine ⟨⟨C,hC⟩,fun t => ?_⟩
  apply lipschitzWith_of_nnnorm_deriv_le
  · change Differentiable ℝ (deriv (value W γ (stripClamp T t)))
    simpa only [iteratedDeriv_one] using (value_contDiff W γ (stripClamp_mem hT0 t).1
      ((stripClamp_mem hT0 t).2.trans_lt hT1)).differentiable_iteratedDeriv 1 (by simp)
  · intro x
    apply NNReal.coe_le_coe.mp
    change |deriv (deriv (value W γ (stripClamp T t))) x| ≤ C
    simpa only [iteratedDeriv_succ,
      iteratedDeriv_zero] using hb (stripClamp T t) (stripClamp_mem hT0 t) x

lemma compactDrift_lipschitz (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∃ L : ℝ≥0, ∀ t, LipschitzWith L (compactDrift W γ T t) := by
  obtain ⟨L,hL⟩ := compactGradient_lipschitz W γ hT0 hT1
  let D : ℝ≥0 := ⟨γ.val ⟨T,⟨hT0,hT1⟩⟩,γ.nonneg _⟩
  refine ⟨D*L,fun t => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hg := (hL t).dist_le_mul x y
  have hc := compactCoeff_bounds γ hT0 hT1 t
  rw [Real.dist_eq,compactDrift,compactDrift,← mul_sub,abs_mul,abs_of_nonneg hc.1,
    NNReal.coe_mul,Real.dist_eq]
  simp only [Real.dist_eq] at hg
  exact (mul_le_mul_of_nonneg_left hg hc.1).trans (by
    change compactCoeff γ T t * ((L:ℝ) * |x-y|) ≤
      γ.val ⟨T,⟨hT0,hT1⟩⟩ * (L:ℝ) * |x-y|
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hc.2 (mul_nonneg L.coe_nonneg (abs_nonneg _)))

lemma compactDrift_eq (W : BrownianSystem Ω) (γ : OrderParameter) {T t : ℝ}
    (ht : t ∈ Icc (0:ℝ) T) (x : ℝ) :
    compactDrift W γ T t x = extend γ.val t*gradient W γ t x := by
  simp only [compactDrift,compactCoeff,compactGradient,stripClamp_eq ht]

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open WeakIto

def diffusionHorizon (n : ℕ) : ℝ := 1-1/((n+2:ℕ):ℝ)

lemma diffusionHorizon_mem (n : ℕ) : diffusionHorizon n ∈ Ico (0:ℝ) 1 := by
  have hd : (0:ℝ) < ((n+2:ℕ):ℝ) := by positivity
  have hge : (1:ℝ) ≤ ((n+2:ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ n+2)
  have hh : (1:ℝ)/((n+2:ℕ):ℝ) ≤ 1 := (div_le_one hd).mpr hge
  have hp : (0:ℝ) < 1/((n+2:ℕ):ℝ) := by positivity
  exact ⟨by unfold diffusionHorizon; linarith,by unfold diffusionHorizon; linarith⟩

lemma diffusionHorizon_tendsto : Tendsto diffusionHorizon atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1-1/((n+2:ℕ):ℝ)) atTop (𝓝 1)
  have hh := (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp (tendsto_add_atTop_nat 2)
  simpa only [diffusionHorizon,sub_zero,Function.comp_apply] using tendsto_const_nhds.sub hh (a := (1:ℝ))

lemma eventually_le_diffusionHorizon {t : ℝ} (ht : t < 1) :
    ∀ᶠ n : ℕ in atTop, t ≤ diffusionHorizon n :=
  (diffusionHorizon_tendsto.eventually (eventually_gt_nhds ht)).mono (fun _ h => h.le)

def diffusionHorizonTime (n : ℕ) : Time := ⟨diffusionHorizon n,diffusionHorizon_mem n⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def stripDrift (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) : BoundedLipschitzDrift where
  f := compactDrift W γ T
  bound := ⟨γ.val T,γ.nonneg T⟩
  lip := (compactDrift_lipschitz W γ T.property.1 T.property.2).choose
  measurable := compactDrift_measurable W γ T.property.1 T.property.2
  bounded := compactDrift_bound W γ T.property.1 T.property.2
  lipschitz := (compactDrift_lipschitz W γ T.property.1 T.property.2).choose_spec

lemma stripDrift_eq (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) (T:ℝ)) (x : ℝ) :
    (stripDrift W γ T).f t x = extend γ.val t*gradient W γ t x := compactDrift_eq W γ ht x

def localDiffusion (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  (stripDrift W γ (diffusionHorizonTime n)).solution W.driver

lemma localDiffusion_progressive (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ) :
    IsProgressive (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable))
      (localDiffusion W γ n) :=
  (stripDrift W γ (diffusionHorizonTime n)).solution_progressive _ W.driver_progressive

lemma localDiffusion_agree (W : BrownianSystem Ω) (γ : OrderParameter) (m n : ℕ)
    (t : ℝ≥0) (hm : (t:ℝ) ≤ diffusionHorizon m) (hn : (t:ℝ) ≤ diffusionHorizon n) (ω : Ω) :
    localDiffusion W γ m t ω = localDiffusion W γ n t ω := by
  apply (stripDrift W γ (diffusionHorizonTime m)).solution_eq_of_agree
    (stripDrift W γ (diffusionHorizonTime n)) _ W.driver_progressive t _ t le_rfl ω
  intro s hs x
  have hst : (s:ℝ) ≤ (t:ℝ) := hs
  rw [stripDrift_eq W γ _ ⟨s.coe_nonneg,hst.trans hm⟩,
    stripDrift_eq W γ _ ⟨s.coe_nonneg,hst.trans hn⟩]

def rawDiffusion (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0) (ω : Ω) : ℝ :=
  atTop.limUnder (fun n => localDiffusion W γ n t ω)

lemma rawDiffusion_progressive (W : BrownianSystem Ω) (γ : OrderParameter) :
    IsProgressive (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable))
      (rawDiffusion W γ) := by
  intro t
  let ℱ := Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)
  have hm (n : ℕ) : StronglyMeasurable[(Subtype.instMeasurableSpace).prod (ℱ t)]
      (fun p : Iic t × Ω => localDiffusion W γ n p.1 p.2) :=
    (localDiffusion_progressive W γ n t).stronglyMeasurable
  let : MeasurableSpace Ω := ℱ t
  exact (StronglyMeasurable.limUnder hm).measurable

lemma rawDiffusion_eq_local (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ diffusionHorizon n) (ω : Ω) :
    rawDiffusion W γ t ω = localDiffusion W γ n t ω := by
  apply Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_le_diffusionHorizon (ht.trans_lt (diffusionHorizon_mem n).2)] with m hm
  exact localDiffusion_agree W γ n m t ht hm ω

lemma rawDiffusion_eq_integral (W : BrownianSystem Ω) (γ : OrderParameter)
    (t : ℝ≥0) (ht : (t:ℝ) < 1) (ω : Ω) :
    rawDiffusion W γ t ω = W.driver t ω+∫ s in (0:ℝ)..(t:ℝ),
      extend γ.val s*gradient W γ s (rawDiffusion W γ (Real.toNNReal s) ω) := by
  obtain ⟨n,hn⟩ := (eventually_le_diffusionHorizon ht).exists
  rw [rawDiffusion_eq_local W γ n t hn]
  rw [localDiffusion, (stripDrift W γ (diffusionHorizonTime n)).solution_eq _ W.driver_progressive]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [uIcc_of_le t.coe_nonneg] at hs
  have hsn : ((Real.toNNReal s):ℝ) ≤ diffusionHorizon n := by
    rw [Real.coe_toNNReal _ hs.1]
    exact hs.2.trans hn
  rw [rawDiffusion_eq_local W γ n (Real.toNNReal s) hsn]
  rw [stripDrift_eq W γ _ ⟨(Real.toNNReal s).coe_nonneg,hsn⟩,Real.coe_toNNReal _ hs.1]
  rfl

def beforeOneGradient (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0) (x : ℝ) : ℝ :=
  if (t:ℝ) < 1 then gradient W γ t x else 0

lemma beforeOneGradient_measurable (W : BrownianSystem Ω) (γ : OrderParameter) :
    Measurable (fun p : ℝ≥0 × ℝ => beforeOneGradient W γ p.1 p.2) := by
  let f (n : ℕ) (p : ℝ≥0 × ℝ) := if (p.1:ℝ) ≤ diffusionHorizon n then
    compactGradient W γ (diffusionHorizon n) p.1 p.2 else 0
  have hm (n : ℕ) : Measurable (f n) := by
    apply Measurable.ite (measurableSet_le (measurable_subtype_coe.comp measurable_fst) measurable_const)
    · exact (compactGradient_continuous W γ (diffusionHorizon_mem n).1
        (diffusionHorizon_mem n).2).measurable.comp
        ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
    · exact measurable_const
  apply measurable_of_tendsto_metrizable hm
  apply tendsto_pi_nhds.mpr
  intro p
  by_cases hp : (p.1:ℝ) < 1
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_le_diffusionHorizon hp] with n hn
    simp only [f,ite_eq_left hn,beforeOneGradient,ite_eq_left hp,compactGradient,
      stripClamp_eq ⟨p.1.coe_nonneg,hn⟩]
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    have hn : ¬ (p.1:ℝ) ≤ diffusionHorizon n :=
      not_le.mpr ((diffusionHorizon_mem n).2.trans_le (not_lt.mp hp))
    simp only [f,ite_eq_right hn,beforeOneGradient,ite_eq_right hp]

lemma beforeOneGradient_bound (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0) (x : ℝ) :
    |beforeOneGradient W γ t x| ≤ 1 := by
  unfold beforeOneGradient
  split_ifs with ht
  · exact gradient_abs_le_one W γ _ _ ht.le
  · norm_num

def rawFeedback (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0) (ω : Ω) : ℝ :=
  beforeOneGradient W γ t (rawDiffusion W γ t ω)

lemma rawFeedback_progressive (W : BrownianSystem Ω) (γ : OrderParameter) :
    IsProgressive (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable))
      (rawFeedback W γ) := by
  intro t
  exact (beforeOneGradient_measurable W γ).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk (rawDiffusion_progressive W γ t))

lemma rawFeedback_bound (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0) (ω : Ω) :
    |rawFeedback W γ t ω| ≤ 1 := beforeOneGradient_bound W γ _ _

lemma rawFeedback_eq (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0)
    (ht : (t:ℝ) < 1) (ω : Ω) :
    rawFeedback W γ t ω = gradient W γ t (rawDiffusion W γ t ω) := by
  simp only [rawFeedback,beforeOneGradient,ite_eq_left ht]

lemma rawDrift_integrable (W : BrownianSystem Ω) (γ : OrderParameter) (ω : Ω) :
    Integrable (fun s : ℝ => extend γ.val s*rawFeedback W γ (Real.toNNReal s) ω) := by
  apply γ.integrable.mul_bdd
    (progressive_time_measurable _ (rawFeedback_progressive W γ) ω).aestronglyMeasurable
  exact Eventually.of_forall (fun _ => rawFeedback_bound W γ _ _)

def diffusion (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0) (ω : Ω) : ℝ :=
  W.driver t ω+∫ s in (0:ℝ)..(t:ℝ), extend γ.val s*rawFeedback W γ (Real.toNNReal s) ω

lemma diffusion_progressive (W : BrownianSystem Ω) (γ : OrderParameter) :
    IsProgressive (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable))
      (diffusion W γ) := by
  have hm : StronglyAdapted (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable))
      (fun t ω => ∫ s in (0:ℝ)..(t:ℝ), extend γ.val s*rawFeedback W γ (Real.toNNReal s) ω) :=
    fun t => (progressive_integral_measurable _ (rawFeedback_progressive W γ) t γ.measurable_extend).stronglyMeasurable
  have hc (ω : Ω) : Continuous (fun t : ℝ≥0 =>
      ∫ s in (0:ℝ)..(t:ℝ), extend γ.val s*rawFeedback W γ (Real.toNNReal s) ω) :=
    (rawDrift_integrable W γ ω).continuous_primitive 0 |>.comp continuous_subtype_val
  exact W.driver_progressive.add (hm.isStronglyProgressive_of_continuous hc).isProgressive

lemma diffusion_eq_raw (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0)
    (ht : (t:ℝ) < 1) (ω : Ω) : diffusion W γ t ω = rawDiffusion W γ t ω := by
  rw [rawDiffusion_eq_integral W γ t ht ω]
  unfold diffusion
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [uIcc_of_le t.coe_nonneg] at hs
  have hs1 : ((Real.toNNReal s):ℝ) < 1 := by rw [Real.coe_toNNReal _ hs.1]; exact hs.2.trans_lt ht
  rw [rawFeedback_eq W γ _ hs1,Real.coe_toNNReal _ hs.1]

lemma diffusion_continuous (W : BrownianSystem Ω) (γ : OrderParameter) :
    ∀ᵐ ω ∂W.law, Continuous (fun t => diffusion W γ t ω) := by
  filter_upwards [W.driver_continuous] with ω hc
  exact hc.add ((rawDrift_integrable W γ ω).continuous_primitive 0 |>.comp continuous_subtype_val)

lemma diffusion_zero (W : BrownianSystem Ω) (γ : OrderParameter) (ω : Ω) : diffusion W γ 0 ω = 0 := by
  simp only [diffusion,NNReal.coe_zero,intervalIntegral.integral_same,W.driver_zero,add_zero]

theorem diffusion_isDiffusion (W : BrownianSystem Ω) (γ : OrderParameter) :
    IsDiffusion W γ (diffusion W γ) := by
  refine ⟨diffusion_progressive W γ,?_⟩
  filter_upwards [diffusion_continuous W γ,W.driver_indistinguishable] with ω hc hB
  refine ⟨(hc.comp (by fun_prop : Continuous Real.toNNReal)).continuousOn,diffusion_zero W γ ω,?_⟩
  intro t ht
  rw [diffusion,hB,Real.coe_toNNReal _ ht.1]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [uIcc_of_le ht.1] at hs
  by_cases hs1 : s < 1
  · have hsn : ((Real.toNNReal s):ℝ) < 1 := by rw [Real.coe_toNNReal _ hs.1]; exact hs1
    rw [rawFeedback_eq W γ _ hsn,Real.coe_toNNReal _ hs.1,diffusion_eq_raw W γ _ hsn]
  · have hse : s = 1 := le_antisymm (hs.2.trans ht.2) (not_lt.mp hs1)
    subst s
    have he : extend γ.val 1 = 0 := by simp [extend]
    simp only [he,zero_mul]

end ZeroTemperatureSK

end
end

end OAI
