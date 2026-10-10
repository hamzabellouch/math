import Mathlib
import OAI.Probability.SKSupport.Density.FiniteDensity
import OAI.Probability.SKSupport.Density.CoerciveMoments
import OAI.Probability.SKSupport.Moments.PositiveGradientError

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

lemma positivePath_sample_limit (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time) :
    ∀ᵐ ξ ∂W.law, Tendsto (fun n => positivePath W γ n (sampleNNTime n t) ξ) atTop
      (𝓝 (diffusion W γ (⟨t,t.property.1⟩:ℝ≥0) ξ)) := by
  filter_upwards [diffusion_continuous W γ] with ξ hc
  have hh := (hc.tendsto (⟨t,t.property.1⟩:ℝ≥0)).comp (sampleNNTime_limit t)
  rw [Metric.tendsto_nhds] at hh ⊢
  intro ε hε
  filter_upwards [positivePath_uniform_error W γ t (ε/2) (by linarith),hh (ε/2) (by linarith)] with n hn hξ
  have h := hn (sampleNNTime n t) (sampleNNTime_le n t) ξ
  apply lt_of_le_of_lt (dist_triangle _ (diffusion W γ (sampleNNTime n t) ξ) _)
  simp only [Real.dist_eq,Function.comp_apply] at *
  linarith

def sampleJet (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ) (t : Time) (m : ℕ) (ξ : Ω) : ℝ :=
  iteratedDeriv m (positiveValue γ n (sampleTime n t)) (positivePath W γ n (sampleNNTime n t) ξ)

def actualJet (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time) (m : ℕ) (ξ : Ω) : ℝ :=
  iteratedDeriv m (value W γ t) (diffusion W γ (⟨t,t.property.1⟩:ℝ≥0) ξ)

lemma sampleJet_limit (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time) (m : ℕ) :
    ∀ᵐ ξ ∂W.law, Tendsto (fun n => sampleJet W γ n t m ξ) atTop (𝓝 (actualJet W γ t m ξ)) := by
  filter_upwards [positivePath_sample_limit W γ t] with ξ hξ
  have hp : Tendsto (fun n => ((sampleTime n t:ℝ),positivePath W γ n (sampleNNTime n t) ξ)) atTop
      (𝓝 ((t:ℝ),diffusion W γ (⟨t,t.property.1⟩:ℝ≥0) ξ)) :=
    (((continuous_subtype_val.tendsto t).comp (sampleTime_limit t))).prodMk_nhds hξ
  have hpw : Tendsto (fun n => ((sampleTime n t:ℝ),positivePath W γ n (sampleNNTime n t) ξ)) atTop
      (𝓝[Icc (0:ℝ) t ×ˢ Set.univ] ((t:ℝ),diffusion W γ (⟨t,t.property.1⟩:ℝ≥0) ξ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hp,Eventually.of_forall (fun n => ?_)⟩
    exact ⟨⟨(sampleTime n t).property.1,sampleNNTime_le n t⟩,mem_univ _⟩
  exact (positiveValue_derivative_uniform W γ t.property.1 t.property.2 m).tendsto_comp
    (value_derivative_continuousOn W γ t.property.1 t.property.2 m _ ⟨⟨t.property.1,le_rfl⟩,mem_univ _⟩) hpw

lemma sampleJet_measurable (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ) (t : Time) (m : ℕ) :
    Measurable (sampleJet W γ n t m) := by
  exact (contDiff_iteratedDeriv_infty (positiveValue_regular γ n (sampleTime n t)).smooth m).continuous.measurable.comp
    ((positiveDrift γ n).solution_measurable W (sampleNNTime n t))

lemma sampleJet_bound (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ξ, |sampleJet W γ n t (m+1) ξ| ≤ C := by
  obtain ⟨C,hC,hb⟩ := positiveValue_uniform_derivative_bounds γ t.property.1 t.property.2 m
  exact ⟨C,hC,fun n ξ => hb n (sampleTime n t) ⟨(sampleTime n t).property.1,sampleNNTime_le n t⟩ _⟩

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

def sampleQuartic (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ) (t : Time) (ξ : Ω) : ℝ :=
  quarticJetPolynomial (positiveCoeff γ n (sampleIndex n t)) (sampleJet W γ n t 2 ξ)

def sampleCoercive (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ) (t : Time) (ξ : Ω) : ℝ :=
  coerciveJetPolynomial (positiveCoeff γ n (sampleIndex n t))
    (sampleJet W γ n t 2 ξ) (sampleJet W γ n t 3 ξ) (sampleJet W γ n t 4 ξ)

lemma sample_coercivity (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time) (n : ℕ)
    (hi : 0 < sampleIndex n t) :
    (1/1000:ℝ)*(∫ ξ, sampleQuartic W γ n t ξ ∂W.law) ≤ ∫ ξ, sampleCoercive W γ n t ξ ∂W.law := by
  have hs := (positiveValue_regular γ n (sampleTime n t)).smooth
  rw [positiveValue_sample] at hs
  have hh := finite_feedback_coercivity W (positiveCoeff γ n) (positiveCoeff_pos γ n)
    (positiveCoeff_monotone γ n) (positiveCoeff_bound γ n)
    (by exact_mod_cast approxMesh_pos n) hi ((sampleIndex_lt n t).le)
  dsimp only at hh
  simp_rw [quarticMoment_scaled hs,coercivePolynomial_scaled hs,← positiveValue_sample γ n t] at hh
  exact hh

lemma sampleQuartic_integral_limit (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht : ContinuousAt γ.val t) :
    Tendsto (fun n => ∫ ξ, sampleQuartic W γ n t ξ ∂W.law) atTop
      (𝓝 (∫ ξ, quarticJetPolynomial (γ.val t) (actualJet W γ t 2 ξ) ∂W.law)) := by
  let := W.isProbability
  obtain ⟨C,hC,hb⟩ := sampleJet_bound W γ t 1
  have hm (n : ℕ) : AEStronglyMeasurable (sampleQuartic W γ n t) W.law := by
    have hh := sampleJet_measurable W γ n t 2
    exact (measurable_const.mul (hh.pow_const 4)).aestronglyMeasurable
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (γ.val t+1)^4*C^4) hm
    (integrable_const _) _ _
  · intro n
    exact Eventually.of_forall (fun ξ => quarticJetPolynomial_bound
      (by rw [abs_of_nonneg (positiveCoeff γ n (sampleIndex n t)).coe_nonneg];exact positiveCoeff_sample_bound γ n t)
      (hb n ξ))
  · filter_upwards [sampleJet_limit W γ t 2] with ξ hξ
    exact ((positiveCoeff_sample_limit γ t ht).pow 4).mul (hξ.pow 4)

lemma sampleCoercive_integral_limit (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht : ContinuousAt γ.val t) :
    Tendsto (fun n => ∫ ξ, sampleCoercive W γ n t ξ ∂W.law) atTop
      (𝓝 (∫ ξ, coerciveJetPolynomial (γ.val t)
        (actualJet W γ t 2 ξ) (actualJet W γ t 3 ξ) (actualJet W γ t 4 ξ) ∂W.law)) := by
  let := W.isProbability
  obtain ⟨A,hA,hbA⟩ := sampleJet_bound W γ t 1
  obtain ⟨B,hB,hbB⟩ := sampleJet_bound W γ t 2
  obtain ⟨C,hC,hbC⟩ := sampleJet_bound W γ t 3
  let D := γ.val t+1
  have hm (n : ℕ) : AEStronglyMeasurable (sampleCoercive W γ n t) W.law := by
    have h2 := sampleJet_measurable W γ n t 2
    have h3 := sampleJet_measurable W γ n t 3
    have h4 := sampleJet_measurable W γ n t 4
    exact (((measurable_const.mul (h4.pow_const 2)).sub ((measurable_const.mul h2).mul (h3.pow_const 2))).add
      (measurable_const.mul (h2.pow_const 4))).aestronglyMeasurable
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => D^2*C^2+12*D^3*A*B^2+6*D^4*A^4) hm
    (integrable_const _) _ _
  · intro n
    exact Eventually.of_forall (fun ξ => coerciveJetPolynomial_bound
      (by rw [abs_of_nonneg (positiveCoeff γ n (sampleIndex n t)).coe_nonneg];exact positiveCoeff_sample_bound γ n t)
      (hbA n ξ) (hbB n ξ) (hbC n ξ))
  · filter_upwards [sampleJet_limit W γ t 2,sampleJet_limit W γ t 3,sampleJet_limit W γ t 4] with ξ h2 h3 h4
    have hc := positiveCoeff_sample_limit γ t ht
    exact (((hc.pow 2).mul (h4.pow 2)).sub (((hc.pow 3).const_mul 12).mul h2 |>.mul (h3.pow 2))).add
      (((hc.pow 4).const_mul 6).mul (h2.pow 4))

theorem actual_coercivity (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht0 : 0 < (t:ℝ)) (ht : ContinuousAt γ.val t) :
    (1/1000:ℝ)*(∫ ξ, quarticJetPolynomial (γ.val t) (actualJet W γ t 2 ξ) ∂W.law) ≤
      ∫ ξ, coerciveJetPolynomial (γ.val t)
        (actualJet W γ t 2 ξ) (actualJet W γ t 3 ξ) (actualJet W γ t 4 ξ) ∂W.law := by
  apply le_of_tendsto_of_tendsto ((sampleQuartic_integral_limit W γ t ht).const_mul (1/1000:ℝ))
    (sampleCoercive_integral_limit W γ t ht)
  filter_upwards [sampleIndex_pos_eventually t ht0] with n hn
  exact sample_coercivity W γ t n hn

end ZeroTemperatureSK

end
end

end OAI
