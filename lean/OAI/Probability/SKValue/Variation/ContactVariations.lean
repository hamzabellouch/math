import Mathlib
import OAI.Probability.SKValue.Variation.FirstVariationCompact

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def OrderParameter.zero : OrderParameter where
  coeff := 0
  nonneg _ _ := le_rfl
  monotone _ _ _ _ _ := le_rfl
  rightContinuous _ _ := continuousWithinAt_const
  integrable := integrableOn_zero

noncomputable def OrderParameter.add (γ η : OrderParameter) : OrderParameter where
  coeff t := γ.coeff t+η.coeff t
  nonneg t ht := add_nonneg (γ.nonneg t ht) (η.nonneg t ht)
  monotone _ hs _ ht hst := add_le_add (γ.monotone hs ht hst) (η.monotone hs ht hst)
  rightContinuous t ht := (γ.rightContinuous t ht).add (η.rightContinuous t ht)
  integrable := γ.integrable.add η.integrable

noncomputable def OrderParameter.atom (s : ℝ) : OrderParameter where
  coeff t := if s≤t then 1 else 0
  nonneg _ _ := by split_ifs <;> norm_num
  monotone t _ u _ htu := by
    by_cases hst : s≤t
    · simp only [ite_eq_left hst,ite_eq_left (hst.trans htu),le_refl]
    · simp only [ite_eq_right hst]; split_ifs <;> norm_num
  rightContinuous t _ := by
    by_cases hst : s≤t
    · apply (continuousWithinAt_const (b := (1 : ℝ))).congr
      · intro u hu
        exact ite_eq_left (hst.trans hu)
      · exact ite_eq_left hst
    · apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
      · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_of_not_ge hst))] with u hu
        exact ite_eq_right (not_le.mpr hu)
      · exact ite_eq_right hst
  integrable := by
    apply Integrable.of_bound
      (StronglyMeasurable.ite measurableSet_Ici stronglyMeasurable_const stronglyMeasurable_const).aestronglyMeasurable 1
    exact Eventually.of_forall (fun t ↦ by split_ifs <;> norm_num)

noncomputable def OrderParameter.removeBelow (γ : OrderParameter) (c : ℝ) : OrderParameter where
  coeff t := max (γ.coeff t-c) 0
  nonneg _ _ := le_max_right _ _
  monotone _ hs _ ht hst := max_le_max (sub_le_sub_right (γ.monotone hs ht hst) c) le_rfl
  rightContinuous t ht := ((γ.rightContinuous t ht).sub continuousWithinAt_const).sup continuousWithinAt_const
  integrable := (γ.integrable.sub (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) 1) (C := c) (by simp))).sup integrableOn_zero

lemma OrderParameter.removeBelow_sub (γ : OrderParameter) (c t : ℝ) :
    (γ.removeBelow c).coeff t-γ.coeff t= -min (γ.coeff t) c := by
  dsimp only [OrderParameter.removeBelow]
  by_cases h : γ.coeff t≤c
  · rw [max_eq_right (sub_nonpos.mpr h),min_eq_left h]; ring
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge h)),min_eq_right (le_of_not_ge h)]; ring

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def contactPotential (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) (s : ℝ) : ℝ :=
  ∫ t in s..1,gradientMoment W γ X t-t

lemma IsDiffusion.moment_difference_integrable {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) :
    IntervalIntegrable (fun t ↦ gradientMoment W γ X t-t) volume 0 1 := by
  have hm := hX.gradientMoment_continuous.aestronglyMeasurable (μ := volume) measurableSet_Ico
  rw [restrict_Ico_eq_restrict_Ioc] at hm
  have hi : IntegrableOn (gradientMoment W γ X) (Ioc (0 : ℝ) 1) :=
    Integrable.of_bound hm 1 (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact gradientMoment_bound W γ X ⟨ht.1.le,ht.2⟩)
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr hi).sub
    (continuous_id.intervalIntegrable 0 1)

lemma integral_atom_mul (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) (f : ℝ → ℝ) :
    (∫ t in (0 : ℝ)..1,(OrderParameter.atom s).coeff t*f t)=∫ t in s..1,f t := by
  have he : (fun t ↦ (OrderParameter.atom s).coeff t*f t)=(Ici s).indicator f := by
    funext t
    simp only [OrderParameter.atom,indicator,mem_Ici]
    split_ifs <;> simp
  have hs' : Ici s∩Icc (0 : ℝ) 1=Icc s 1 := by
    ext t
    simp only [mem_inter_iff,mem_Ici,mem_Icc]
    constructor
    · rintro ⟨hst,_,ht1⟩; exact ⟨hst,ht1⟩
    · rintro ⟨hst,ht1⟩; exact ⟨hst,hs.1.trans hst,ht1⟩
  rw [he,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),
    ←integral_Icc_eq_integral_Ioc,integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici,hs',
    intervalIntegral.integral_of_le hs.2,integral_Icc_eq_integral_Ioc]

lemma IsMinimizer.contactPotential_nonneg {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hγ : IsMinimizer W γ) (hX : IsDiffusion W γ X)
    {s : ℝ} (hs : s∈Icc (0 : ℝ) 1) : 0≤contactPotential W γ X s := by
  have hh := hγ.variation_inequality hX (γ.add (OrderParameter.atom s))
  simp only [OrderParameter.add,add_sub_cancel_left] at hh
  rwa [integral_atom_mul s hs] at hh

lemma IsDiffusion.contactPotential_continuous {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) :
    ContinuousOn (contactPotential W γ X) (Icc (0 : ℝ) 1) := by
  change ContinuousOn (fun s : ℝ ↦ ∫ t in s..1,gradientMoment W γ X t-t) (Icc (0 : ℝ) 1)
  have hi : IntegrableOn (fun t ↦ gradientMoment W γ X t-t) (uIcc (0 : ℝ) 1) volume := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ)≤1)).mp
      hX.moment_difference_integrable
  have hc : ContinuousOn (fun s : ℝ ↦ ∫ t in s..1,gradientMoment W γ X t-t) (uIcc (0 : ℝ) 1) :=
    intervalIntegral.continuousOn_primitive_interval_left hi
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hc

lemma IsDiffusion.contactPotential_hasDerivAt {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {s : ℝ} (hs : s∈Ioo (0 : ℝ) 1) :
    HasDerivAt (contactPotential W γ X) (s-gradientMoment W γ X s) s := by
  change HasDerivAt (fun u : ℝ ↦ ∫ t in u..1,gradientMoment W γ X t-t) _ s
  have hc : ContinuousOn (fun t ↦ gradientMoment W γ X t-t) (Ico (0 : ℝ) 1) :=
    hX.gradientMoment_continuous.sub continuousOn_id
  have hns : Ico (0 : ℝ) 1∈𝓝 s := mem_of_superset (Ioo_mem_nhds hs.1 hs.2) Ioo_subset_Ico_self
  have hi : IntervalIntegrable (fun t ↦ gradientMoment W γ X t-t) volume s 1 :=
    hX.moment_difference_integrable.mono_set (by
      rw [uIcc_of_le hs.2.le,uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
      exact Icc_subset_Icc hs.1.le le_rfl)
  have hh : HasDerivAt (fun u : ℝ ↦ ∫ t in u..1,gradientMoment W γ X t-t)
      (-(gradientMoment W γ X s-s)) s := intervalIntegral.integral_hasDerivAt_left hi
        (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hc.mono Ioo_subset_Ico_self) s hs)
        (hc.continuousAt hns)
  simpa only [neg_sub] using hh

lemma IsMinimizer.moment_eq_at_contact {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hγ : IsMinimizer W γ) (hX : IsDiffusion W γ X)
    {s : ℝ} (hs : s∈Ioo (0 : ℝ) 1) (hG : contactPotential W γ X s=0) :
    gradientMoment W γ X s=s := by
  have hm : IsLocalMin (contactPotential W γ X) s := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    rw [hG]
    exact hγ.contactPotential_nonneg hX ⟨ht.1.le,ht.2.le⟩
  have hz := hm.hasDerivAt_eq_zero (hX.contactPotential_hasDerivAt hs)
  linarith

end SKValue

end

end OAI
