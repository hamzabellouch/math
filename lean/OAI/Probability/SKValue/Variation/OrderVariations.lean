import Mathlib
import OAI.Probability.SKValue.Control.Regularity

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def OrderParameter.mix (γ η : OrderParameter) (ε : ℝ)
    (hε : ε∈Icc (0 : ℝ) 1) : OrderParameter where
  coeff t := (1-ε)*γ.coeff t+ε*η.coeff t
  nonneg t ht := add_nonneg (mul_nonneg (sub_nonneg.mpr hε.2) (γ.nonneg t ht))
    (mul_nonneg hε.1 (η.nonneg t ht))
  monotone _s hs _t ht hst := add_le_add
    (mul_le_mul_of_nonneg_left (γ.monotone hs ht hst) (sub_nonneg.mpr hε.2))
    (mul_le_mul_of_nonneg_left (η.monotone hs ht hst) hε.1)
  rightContinuous t ht := ((γ.rightContinuous t ht).const_mul _).add ((η.rightContinuous t ht).const_mul _)
  integrable := (γ.integrable.const_mul _).add (η.integrable.const_mul _)

lemma OrderParameter.mix_coeff_sub (γ η : OrderParameter) {ε : ℝ} (hε : ε∈Icc (0 : ℝ) 1) (t : ℝ) :
    (γ.mix η ε hε).coeff t-γ.coeff t=ε*(η.coeff t-γ.coeff t) := by dsimp [OrderParameter.mix]; ring

lemma OrderParameter.mix_cutoff_sub (γ η : OrderParameter) {ε : ℝ} (hε : ε∈Icc (0 : ℝ) 1) (t : ℝ) :
    (γ.mix η ε hε).cutoff t-γ.cutoff t=ε*(η.cutoff t-γ.cutoff t) := by
  by_cases ht : t∈Ico (0 : ℝ) 1
  · simp only [OrderParameter.cutoff,indicator_of_mem ht]
    exact γ.mix_coeff_sub η hε t
  · simp only [OrderParameter.cutoff,indicator_of_notMem ht,sub_self,mul_zero]

lemma OrderParameter.mix_difference_integral (γ η : OrderParameter) {ε : ℝ}
    (hε : ε∈Icc (0 : ℝ) 1) (a b : ℝ) :
    (∫ t in a..b,|(γ.mix η ε hε).cutoff t-γ.cutoff t|)=
      ε*(∫ t in a..b,|η.cutoff t-γ.cutoff t|) := by
  simp_rw [γ.mix_cutoff_sub η hε,abs_mul,abs_of_nonneg hε.1]
  exact intervalIntegral.integral_const_mul ε _

lemma OrderParameter.mix_strip_difference_bound (γ η : OrderParameter) {ε T : ℝ}
    (hε : ε∈Icc (0 : ℝ) 1) (hT : T∈Ico (0 : ℝ) 1) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    |(γ.mix η ε hε).coeff t-γ.coeff t|≤ε*(η.coeff T+γ.coeff T) := by
  rw [γ.mix_coeff_sub η hε,abs_mul,abs_of_nonneg hε.1]
  apply mul_le_mul_of_nonneg_left _ hε.1
  have ht' : t∈Ico (0 : ℝ) 1 := ⟨ht.1,ht.2.trans_lt hT.2⟩
  calc |η.coeff t-γ.coeff t|≤|η.coeff t|+|γ.coeff t| := abs_sub _ _
    _=η.coeff t+γ.coeff t := by rw [abs_of_nonneg (η.nonneg t ht'),abs_of_nonneg (γ.nonneg t ht')]
    _≤η.coeff T+γ.coeff T := add_le_add (η.monotone ht' hT ht.2) (γ.monotone ht' hT ht.2)

lemma OrderParameter.weighted_intervalIntegrable (γ : OrderParameter) :
    IntervalIntegrable (fun t ↦ t*γ.coeff t) volume 0 1 :=
  γ.intervalIntegrable.continuousOn_mul continuousOn_id

lemma IsMinimizer.mix_value_inequality {W : BrownianSpace} {γ : OrderParameter}
    (hγ : IsMinimizer W γ) (η : OrderParameter) {ε : ℝ} (hε : ε∈Icc (0 : ℝ) 1) :
    (ε/2)*(∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t))≤
      phi W (γ.mix η ε hε) 0 0-phi W γ 0 0 := by
  have hh := hγ (γ.mix η ε hε)
  have hi : (∫ t in (0 : ℝ)..1,t*(γ.mix η ε hε).coeff t)-
      (∫ t in (0 : ℝ)..1,t*γ.coeff t)=ε*(∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t)) := by
    rw [←intervalIntegral.integral_sub (γ.mix η ε hε).weighted_intervalIntegrable γ.weighted_intervalIntegrable,
      ←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [OrderParameter.mix]
    ring
  dsimp only [parisi] at hh
  linarith

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def gradientMoment (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) (t : ℝ) : ℝ := ∫ ω,(gradient W γ t (X t ω))^2 ∂W.μ

lemma gradientMoment_nonneg (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) (t : ℝ) : 0≤gradientMoment W γ X t :=
  integral_nonneg (fun _ ↦ sq_nonneg _)

lemma gradientMoment_bound (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    |gradientMoment W γ X t|≤1 := by
  simpa only [gradientMoment,Real.norm_eq_abs,probReal_univ,mul_one] using
    (norm_integral_le_of_norm_le_const (μ := W.μ) (C := (1 : ℝ))
      (f := fun ω ↦ (gradient W γ t (X t ω))^2)
      (Eventually.of_forall (fun ω ↦ by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact (sq_le_one_iff_abs_le_one _).mpr (gradient_bound W γ ht _))))

lemma IsDiffusion.gradientMoment_continuous {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) :
    ContinuousOn (gradientMoment W γ X) (Ico (0 : ℝ) 1) := by
  intro t ht
  obtain ⟨T,htT,hT1⟩ := exists_between ht.2
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := sourceStripRegularity W γ T ⟨ht.1.trans htT.le,hT1⟩
  have hc := mean_derivative_square_continuous (by norm_num : (0 : ℝ)≤1) hLu
    (fun s hs ↦ (hV.smooth s hs).continuous_deriv (by norm_num)) hV.bounded hu
    (fun s hs ↦ (hX.measurable ⟨hs.1,hs.2.trans hT1.le⟩).aestronglyMeasurable)
    (hX.2.mono (fun _ hω ↦ hω.1.mono (Icc_subset_Icc le_rfl hT1.le)))
  apply (hc t ⟨ht.1,htT.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT)] with s hs hsT
  exact ⟨hs.1,hsT.le⟩

lemma IsDiffusion.weightedMoment_integrable {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (η : OrderParameter) :
    IntervalIntegrable (fun t ↦ η.coeff t*gradientMoment W γ X t) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
  have hm := hX.gradientMoment_continuous.aestronglyMeasurable (μ := volume) measurableSet_Ico
  rw [restrict_Ico_eq_restrict_Ioc] at hm
  exact η.integrable.mul_bdd hm (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs] using gradientMoment_bound W γ X ⟨ht.1.le,ht.2⟩)

lemma IsDiffusion.weightedMean_integrable {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (η : OrderParameter) :
    IntervalIntegrable (fun t ↦ η.coeff t*(∫ ω,(1/2 : ℝ)*(gradient W γ t (X t ω))^2 ∂W.μ)) volume 0 1 := by
  have hi := (hX.weightedMoment_integrable η).const_mul (1/2 : ℝ)
  simpa only [integral_const_mul,mul_left_comm,gradientMoment] using hi

lemma IsDiffusion.mix_moment_integral {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (η : OrderParameter)
    {ε T : ℝ} (hε : ε∈Icc (0 : ℝ) 1) (hT : T∈Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..T,(γ.mix η ε hε).coeff t*(∫ ω,(1/2 : ℝ)*(gradient W γ t (X t ω))^2 ∂W.μ))-
    (∫ t in (0 : ℝ)..T,γ.coeff t*(∫ ω,(1/2 : ℝ)*(gradient W γ t (X t ω))^2 ∂W.μ))=
    (ε/2)*(∫ t in (0 : ℝ)..T,(η.coeff t-γ.coeff t)*gradientMoment W γ X t) := by
  have ht : uIcc (0 : ℝ) T⊆uIcc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le hT.1,uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using Icc_subset_Icc le_rfl hT.2
  rw [←intervalIntegral.integral_sub ((hX.weightedMean_integrable _).mono_set ht)
    ((hX.weightedMean_integrable _).mono_set ht),←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [integral_const_mul]
  dsimp only [OrderParameter.mix,gradientMoment]
  ring

end SKValue

end

end OAI
