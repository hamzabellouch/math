import Mathlib
import OAI.Probability.SKSupport.Moments.ThirdFields
import OAI.Probability.SKSupport.Moments.StrictMoments
import OAI.Probability.SKSupport.Density.SampleJets

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactJet_eq_value (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) (n : ℕ) (x : ℝ) :
    compactJet W γ T n t x=iteratedDeriv (n+1) (value W γ t) x := by
  unfold compactJet compactGradient gradient
  rw [stripClamp_eq ht,iteratedDeriv_succ']

lemma stripSecond_eq_actual (W : BrownianSystem Ω) (γ : OrderParameter) (T t : Time)
    (htT : t ≤ T) (c : ℝ) :
    stripSecond W γ T c t = ∫ ξ, (actualJet W γ t 3 ξ)^2-2*c*(actualJet W γ t 2 ξ)^3 ∂W.law := by
  unfold stripSecond TimeField.expected
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [secondCurvatureField_eq]
  have heNN : Real.toNNReal (t:ℝ)=(⟨t,t.property.1⟩:ℝ≥0) := by ext;exact Real.coe_toNNReal _ t.property.1
  rw [heNN]
  have hd := diffusion_eq_strip W γ T (⟨t,t.property.1⟩:ℝ≥0) htT ξ
  rw [← hd,compactJet_eq_value W γ T ⟨t.property.1,htT⟩,
    compactJet_eq_value W γ T ⟨t.property.1,htT⟩]
  rfl

lemma stripThird_eq_actual (W : BrownianSystem Ω) (γ : OrderParameter) (T t : Time)
    (htT : t ≤ T) (c : ℝ) :
    stripThird W γ T c t = ∫ ξ, (actualJet W γ t 4 ξ)^2-
      12*c*actualJet W γ t 2 ξ*(actualJet W γ t 3 ξ)^2+6*c^2*(actualJet W γ t 2 ξ)^4 ∂W.law := by
  unfold stripThird TimeField.expected
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [thirdCurvatureField_eq]
  have heNN : Real.toNNReal (t:ℝ)=(⟨t,t.property.1⟩:ℝ≥0) := by ext;exact Real.coe_toNNReal _ t.property.1
  rw [heNN]
  have hd := diffusion_eq_strip W γ T (⟨t,t.property.1⟩:ℝ≥0) htT ξ
  rw [← hd,compactJet_eq_value W γ T ⟨t.property.1,htT⟩,
    compactJet_eq_value W γ T ⟨t.property.1,htT⟩,compactJet_eq_value W γ T ⟨t.property.1,htT⟩]
  rfl

lemma actualQuartic_pos (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht : 0 < (t:ℝ)) : 0 < ∫ ξ, (actualJet W γ t 2 ξ)^4 ∂W.law := by
  apply actual_jet_even_moment_pos W γ t ht 1 2 (by norm_num)
  have hn := curvature_not_identically_zero W γ t.property.1 t.property.2
  change ∃ x, deriv (deriv (value W γ t)) x ≠ 0 at hn
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hn

lemma actualThirdSquare_pos (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht : 0 < (t:ℝ)) : 0 < ∫ ξ, (actualJet W γ t 3 ξ)^2 ∂W.law := by
  apply actual_jet_even_moment_pos W γ t ht 2 1 (by norm_num)
  have hn := third_not_identically_zero W γ t.property.1 t.property.2
  change ∃ x, deriv (deriv (deriv (value W γ t))) x ≠ 0 at hn
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hn

lemma stripThird_coercive (W : BrownianSystem Ω) (γ : OrderParameter) (T t : Time)
    (ht : 0 < (t:ℝ)) (htT : t ≤ T) (hcont : ContinuousAt γ.val t) :
    (1/1000:ℝ)*(γ.val t)^4*(∫ ξ, (actualJet W γ t 2 ξ)^4 ∂W.law) ≤
      (γ.val t)^2 * stripThird W γ T (γ.val t) t := by
  have hh := actual_coercivity W γ t ht hcont
  have hl : (∫ ξ, quarticJetPolynomial (γ.val t) (actualJet W γ t 2 ξ) ∂W.law)=
      (γ.val t)^4*(∫ ξ, (actualJet W γ t 2 ξ)^4 ∂W.law) := by
    exact integral_const_mul _ _
  have hr : (∫ ξ, coerciveJetPolynomial (γ.val t)
      (actualJet W γ t 2 ξ) (actualJet W γ t 3 ξ) (actualJet W γ t 4 ξ) ∂W.law)=
      (γ.val t)^2 * stripThird W γ T (γ.val t) t := by
    rw [stripThird_eq_actual W γ T t htT,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ξ
    unfold coerciveJetPolynomial
    ring
  rw [hl,hr] at hh
  simpa only [mul_assoc] using hh

lemma stripThird_pos (W : BrownianSystem Ω) (γ : OrderParameter) (T t : Time)
    (ht : 0 < (t:ℝ)) (htT : t ≤ T) (hcont : ContinuousAt γ.val t) (hc : 0 < γ.val t) :
    0 < stripThird W γ T (γ.val t) t := by
  have hp := actualQuartic_pos W γ t ht
  have hh := stripThird_coercive W γ T t ht htT hcont
  have hl : 0 < (1/1000:ℝ)*(γ.val t)^4*(∫ ξ, (actualJet W γ t 2 ξ)^4 ∂W.law) := by positivity
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hc)).mp (hl.trans_le hh)

lemma stripSecond_zero_pos (W : BrownianSystem Ω) (γ : OrderParameter) (T t : Time)
    (ht : 0 < (t:ℝ)) (htT : t ≤ T) : 0 < stripSecond W γ T 0 t := by
  rw [stripSecond_eq_actual W γ T t htT]
  simp only [mul_zero,zero_mul,sub_zero]
  exact actualThirdSquare_pos W γ t ht

end ZeroTemperatureSK

end
end

end OAI
