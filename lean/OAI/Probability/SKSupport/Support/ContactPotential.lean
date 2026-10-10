import Mathlib
import OAI.Probability.SKSupport.Support.TerminalCurvature
import OAI.Probability.SKSupport.Backward.TerminalTransition
import OAI.Probability.SKSupport.Density.DensityHeat
import OAI.Probability.SKSupport.Diffusion.Diffusion
import OAI.Probability.SKSupport.Support.VariationIntegrals
import OAI.Probability.SKSupport.Support.CDFParameters

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

def contactPotential (W : BrownianSystem Ω) (γ : OrderParameter) (s : ℝ) : ℝ :=
  ∫ t in s..1, squareMoment W γ (diffusion W γ) t-t

lemma squareMoment_integrable (W : BrownianSystem Ω) (γ : OrderParameter) :
    IntervalIntegrable (squareMoment W γ (diffusion W γ)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ico_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply IntegrableOn.of_bound measure_Ico_lt_top ((squareMoment_continuousOn W γ).aestronglyMeasurable measurableSet_Ico) 1
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  simpa only [Real.norm_eq_abs] using (squareMoment_bounds W γ ht.2.le).2

lemma contactIntegrand_integrable (W : BrownianSystem Ω) (γ : OrderParameter) :
    IntervalIntegrable (fun t => squareMoment W γ (diffusion W γ) t-t) volume 0 1 :=
  (squareMoment_integrable W γ).sub (continuous_id.intervalIntegrable 0 1)

lemma contactPotential_continuousOn (W : BrownianSystem Ω) (γ : OrderParameter) :
    ContinuousOn (contactPotential W γ) (Icc (0:ℝ) 1) := by
  have hi : IntegrableOn (fun t => squareMoment W γ (diffusion W γ) t-t) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp (contactIntegrand_integrable W γ)
  unfold contactPotential
  simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using intervalIntegral.continuousOn_primitive_interval_left hi

lemma contactIntegrand_tail_integrable (W : BrownianSystem Ω) (γ : OrderParameter) {s : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) :
    IntervalIntegrable (fun t => squareMoment W γ (diffusion W γ) t-t) volume s 1 := by
  apply (contactIntegrand_integrable W γ).mono_set
  rw [uIcc_of_le hs.2,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact Icc_subset_Icc_left hs.1

lemma contactPotential_hasDerivAt (W : BrownianSystem Ω) (γ : OrderParameter) {s : ℝ}
    (hs : s ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (contactPotential W γ) (s-squareMoment W γ (diffusion W γ) s) s := by
  have hc : ContinuousOn (fun t => squareMoment W γ (diffusion W γ) t-t) (Ioo (0:ℝ) 1) :=
    ((squareMoment_continuousOn W γ).mono Ioo_subset_Ico_self).sub continuousOn_id
  have hh := intervalIntegral.integral_hasDerivAt_left (contactIntegrand_tail_integrable W γ ⟨hs.1.le,hs.2.le⟩)
    (hc.stronglyMeasurableAtFilter isOpen_Ioo _ hs) (hc.continuousAt (Ioo_mem_nhds hs.1 hs.2))
  unfold contactPotential
  simpa only [neg_sub] using hh

lemma contactPotential_nonneg (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ)
    (s : Time) : 0 ≤ contactPotential W γ s := by
  have hn := minimizer_variational_inequality W γ hmin (γ.addCDF (Measure.dirac s))
  simp only [OrderParameter.addCDF_difference] at hn
  rw [finiteCDF_fubini (contactIntegrand_integrable W γ),integral_dirac] at hn
  exact hn

lemma contactPotential_remove (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ)
    {μ ν : Measure Time} [IsFiniteMeasure ν] (hμ : IsStieltjesMeasure γ μ) (hν : ν ≤ μ) :
    ∫ s : Time, contactPotential W γ s ∂ν ≤ 0 := by
  have hn := minimizer_variational_inequality W γ hmin (γ.removeCDF hμ hν)
  simp only [OrderParameter.removeCDF_difference,neg_mul,intervalIntegral.integral_neg] at hn
  rw [finiteCDF_fubini (contactIntegrand_integrable W γ)] at hn
  change 0 ≤ -(∫ s : Time, contactPotential W γ s ∂ν) at hn
  linarith

lemma contactPotential_compact_mass_removal (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ)
    {μ : Measure Time} (hμ : IsStieltjesMeasure γ μ) (K : Set Time) (hK : IsCompact K) :
    ∫ s in K, contactPotential W γ s ∂μ ≤ 0 := by
  let : IsFiniteMeasureOnCompacts μ := (stieltjes_deterministic γ hμ).finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ];exact hK.measure_lt_top⟩
  exact contactPotential_remove W γ hmin hμ Measure.restrict_le_self

theorem minimizer_contact (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ)
    {μ : Measure Time} (hμ : IsStieltjesMeasure γ μ) :
    ∀ t, SupportDeterministic.InSupport μ t →
      squareMoment W γ (diffusion W γ) t=t ∧ curvatureMoment W γ t ≤ 1 := by
  apply SupportDeterministic.Variation.contact_conditions (stieltjes_deterministic γ hμ)
    ((contactPotential_continuousOn W γ).mono Ico_subset_Icc_self)
  · exact fun t ht => contactPotential_nonneg W γ hmin ⟨t,ht⟩
  · exact contactPotential_compact_mass_removal W γ hmin hμ
  · exact squareMoment_zero W γ
  · intro t ht
    exact (squareMoment_hasDerivWithinAt W γ ht.1 ht.2).mono (Ici_subset_Ici.mpr ht.1)
  · intro t ht
    exact contactPotential_hasDerivAt W γ ht

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma gradientDefect_nonneg (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ} (ht : t ≤ 1) (x : ℝ) :
    0 ≤ 1-(gradient W γ t x)^2 := by
  have hh := abs_le.mp (gradient_abs_le_one W γ t x ht)
  nlinarith

lemma terminal_plateau_denominator (W : BrownianSystem Ω) (γ : OrderParameter)
    {a c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ r ∈ Ioo a 1, extend γ.val r=c)
    (s T : Time) (has : a < (s:ℝ)) (hsT : s ≤ T) {x : ℝ} (hx : |x| ≤ 1) :
    varianceHeat ((T:ℝ)-s) (fun y => Real.exp (c*value W γ T y)) x ≤
      Real.exp (c*(value W γ s 0+1)) := by
  rw [varianceHeat_exp_eq_exp_log (value_lipschitz W γ T T.property.2.le),
    ← value_plateau_semigroup W γ hc0 s.property.1 has hsT T.property.2 hc]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hc0
  have hh := (value_lipschitz W γ s s.property.2.le).norm_sub_le x 0
  simp only [Real.norm_eq_abs,NNReal.coe_one,one_mul,sub_zero] at hh
  linarith [le_abs_self (value W γ s x-value W γ s 0)]

lemma terminal_plateau_second_moment_defect (W : BrownianSystem Ω) (γ : OrderParameter)
    {a c : ℝ} (ha : a < 1) (hc0 : 0 ≤ c) (hc : ∀ r ∈ Ioo a 1, extend γ.val r=c)
    (s : Time) (hs0 : 0 < (s:ℝ)) (has : a < (s:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : Time, ((s:ℝ)+1)/2 ≤ T →
      8*kernelConstant*c*Real.sqrt (1-(T:ℝ)) ≤ 1/2 →
      C*Real.sqrt (1-(T:ℝ)) ≤ 1-squareMoment W γ (diffusion W γ) T := by
  let := W.isProbability
  let δ : ℝ := (1-(s:ℝ))/2
  have hδ : 0 < δ := by dsimp [δ];linarith [s.property.2]
  let M : ℝ := Real.exp (c*(value W γ s 0+1))
  have hM : 0 < M := Real.exp_pos _
  let E : Set Ω := {ξ | diffusion W γ (⟨s,s.property.1⟩:ℝ≥0) ξ ∈ Ioo (-1:ℝ) 1}
  have hmX : Measurable (diffusion W γ (⟨s,s.property.1⟩:ℝ≥0)) :=
    ((diffusion_progressive W γ).adapted _).mono (Filtration.le _ _) le_rfl
  have hE : MeasurableSet E := hmX measurableSet_Ioo
  have hEpos : 0 < W.law.real E := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt (diffusion_interval_pos W γ s hs0 (show (-1:ℝ) < 1 by norm_num))
    · exact measure_ne_top _ _
  let K : ℝ := ((3/2:ℝ)*(Real.sqrt (2*Real.pi))⁻¹*Real.exp (-2/δ))/(M*(4*kernelConstant+2))
  have hκ := kernelConstant_nonneg
  have hK : 0 < K := by dsimp [K];positivity
  refine ⟨W.law.real E*K,mul_pos hEpos hK,fun T hsT hsmall => ?_⟩
  have hst : s ≤ T := by change (s:ℝ) ≤ T;linarith [s.property.2]
  let r : ℝ := Real.sqrt (1-(T:ℝ))/(4*kernelConstant+2)
  have hr0 : 0 ≤ r := by dsimp [r];positivity
  have hr1 : r ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*kernelConstant+2)).mpr
    have hr := Real.sqrt_le_one.mpr (show 1-(T:ℝ) ≤ 1 by linarith [T.property.1])
    linarith
  let g : ℝ → ℝ := fun y => 1-(gradient W γ T y)^2
  have hg := gradientDefect_smooth W γ T.property.1 T.property.2
  have hf := value_regular W γ T.property.1 T.property.2
  have hLip := value_lipschitz W γ T T.property.2.le
  have hg0 : ∀ y, 0 ≤ g y := gradientDefect_nonneg W γ T.property.2.le
  have hgwin : ∀ y, |y| ≤ r → 3/4 ≤ g y := by
    intro y hy
    have hu := abs_le.mp (gradient_terminal_small W γ hc0
      (parameter_bound_of_terminal_plateau γ ha hc) T.property.1 T.property.2 hsmall hy)
    dsimp [g]
    nlinarith
  let F : Ω → ℝ := fun ξ => varianceTilted c ((T:ℝ)-s) (value W γ T) g
    (diffusion W γ (⟨s,s.property.1⟩:ℝ≥0) ξ)
  have hfi : Integrable F W.law := integrable_family_comp (varianceTilted_family hf hLip hg hc0) _ hmX
  have hF0 : ∀ ξ, 0 ≤ F ξ := by
    intro ξ
    dsimp [F]
    rw [varianceTilted_eq_tiltedMean hLip.continuous.measurable hg.smooth.continuous.measurable]
    exact tiltedMean_nonneg hLip hg0 c _ _
  have hlower : ∀ ξ ∈ E, K*Real.sqrt (1-(T:ℝ)) ≤ F ξ := by
    intro ξ hξ
    have hx : |diffusion W γ (⟨s,s.property.1⟩:ℝ≥0) ξ| ≤ 1 := abs_le.mpr ⟨hξ.1.le,hξ.2.le⟩
    have hh := varianceTilted_lower_window hLip hg hc0
      (fun y => (abs_nonneg y).trans (abs_le_value W γ T y T.property.2.le)) hg0 hδ
      (show δ ≤ (T:ℝ)-s by dsimp [δ];linarith)
      (show (T:ℝ)-s ≤ 1 by linarith [T.property.2,s.property.1]) hr0 hr1 hx hgwin
      (terminal_plateau_denominator W γ hc0 hc s T has hst hx)
    have he : ((3/2:ℝ)*(Real.sqrt (2*Real.pi))⁻¹*Real.exp (-2/δ)*r)/M=K*Real.sqrt (1-(T:ℝ)) := by
      dsimp [r,K]
      rw [mul_div_assoc,div_div, mul_comm (4*kernelConstant+2) M]
      ring
    rw [he] at hh
    exact hh
  have hint := setIntegral_mono_on (f := fun _ => K*Real.sqrt (1-(T:ℝ)))
    (integrable_const _).integrableOn hfi.integrableOn hE hlower
  rw [setIntegral_const,smul_eq_mul] at hint
  have hb := hint.trans (setIntegral_le_integral hfi (Eventually.of_forall hF0))
  have htrans := terminal_plateau_transition W γ hc0 hc s T has hst hg
  have hiq : Integrable (fun ξ => (gradient W γ T (diffusion W γ (⟨T,T.property.1⟩:ℝ≥0) ξ))^2) W.law := by
    have hmT : Measurable (diffusion W γ (⟨T,T.property.1⟩:ℝ≥0)) :=
      ((diffusion_progressive W γ).adapted _).mono (Filtration.le _ _) le_rfl
    have hu := hf.deriv_bounded
    have hsq : BoundedSmooth (fun y => (gradient W γ T y)^2) := by simpa only [gradient,pow_two] using hu.mul hu
    obtain ⟨G,hG⟩ := hsq.bound
    exact Integrable.of_bound (hsq.smooth.continuous.measurable.comp hmT).aestronglyMeasurable G (Eventually.of_forall (fun ξ => hG _))
  have he : (∫ ξ, g (diffusion W γ (⟨T,T.property.1⟩:ℝ≥0) ξ) ∂W.law)=1-squareMoment W γ (diffusion W γ) T := by
    dsimp [g]
    rw [integral_sub (integrable_const _) hiq,integral_const]
    simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul,squareMoment]
    congr 2
    funext ξ
    congr 3
    exact (Real.toNNReal_coe (r := (⟨T,T.property.1⟩:ℝ≥0))).symm
  rw [← htrans,he] at hb
  simpa only [mul_assoc] using hb

end ZeroTemperatureSK

end
end

end OAI
