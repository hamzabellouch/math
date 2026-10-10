import Mathlib
import OAI.Probability.LogConcave.Sampling.CenteringOutputLaw
import OAI.Probability.LogConcave.Numerics.DerivSetIntegral
import OAI.Probability.LogConcave.Sampling.TerminalMean
import OAI.Probability.LogConcave.Numerics.GradientBound

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function Filter MeasureTheory
open scoped NNReal Topology RealInnerProductSpace

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

include hlam in

theorem centeringKernel_weak (u : Point d) {φ : Point d → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫y,inner ℝ u (conditionalFieldMean F x r T y-
      ∫z,primitiveField F x r z ∂gibbs (primitivePotential F x r))*φ y ∂interpolationLaw F x r T)=
      ∫y,fderiv ℝ φ y ((centeringKernel hF x hr hl hT0 hT1 y).adjoint u) ∂interpolationLaw F x r T := by
  let μ := interpolationLaw F x r T
  let : IsProbabilityMeasure μ := interpolationLaw_probability hF x hr.le (by linarith only [hl]) T
  let M := fun p => inner ℝ u (terminalMean hF x hr hl hT0 hT1 p)
  let A := fun t => ∫y,M (t,y)*φ y ∂μ
  let B := fun t => ∫y,fderiv ℝ φ y (steinIntegrand hF x hr hl hT0 hT1 (t,y) u) ∂μ
  have hM : ContDiff ℝ 1 M := ((contDiff_const (c:=u)).inner ℝ
    (terminalMean_smooth hF x hr hl hT0 hT1)).of_le (by simp)
  have hA (t : ℝ) : HasDerivAt A (∫y,fderiv ℝ M (t,y) (1,0)*φ y ∂μ) t :=
    CompactExpectation.compact_test_hasDerivAt hM hφ hφc t
  have hAc : Continuous A := continuous_iff_continuousAt.mpr (fun t => (hA t).continuousAt)
  have hXi := (steinIntegrand_smooth hF x hr hlam hl hT0 hT1).continuous
  have hBc : Continuous B := GradientIntegral.continuous_gradient_expectation hφ hφc hXi u
  have hAd (t : ℝ) (ht : t∈Ioo (0:ℝ) T) : HasDerivAt A (B t) t := by
    have he := stein_weak_derivative hF x hr hlam hl hT0 hT1 ht.1 ht.2 u hφ hφc
    change (∫y,fderiv ℝ M (t,y) (1,0)*φ y ∂μ)=B t at he
    exact (hA t).congr_deriv he
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT0 hAc.continuousOn hAd (hBc.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_of_le hT0,←integral_Icc_eq_integral_Ioc] at hFTC
  have hBound : ∀t∈Icc (0:ℝ) T,∀y,‖steinIntegrand hF x hr hl hT0 hT1 (t,y)‖≤
      (Real.exp (Real.pi^2/4)*(Real.pi^2/2))*((lam:ℝ)*r) :=
    fun t ht y => steinIntegrand_norm_le hF x hr hlam hl hT0 hT1 ⟨t,ht⟩ y
  have hExchange := GradientIntegral.gradient_exchange (μ:=μ) hφ hφc hXi
    (by positivity : 0≤(Real.exp (Real.pi^2/4)*(Real.pi^2/2))*((lam:ℝ)*r)) hBound u
  change (∫t in Icc (0:ℝ) T,B t)=_ at hExchange
  have hInt (t : ℝ) : Integrable (fun y => M (t,y)*φ y) μ :=
    (((hM.continuous.comp (continuous_const.prodMk continuous_id)).mul hφ.continuous)).integrable_of_hasCompactSupport hφc.mul_left
  have hEnds : A T-A 0=(∫y,inner ℝ u (conditionalFieldMean F x r T y-
      ∫z,primitiveField F x r z ∂gibbs (primitivePotential F x r))*φ y ∂μ) := by
    rw [← integral_sub (hInt T) (hInt 0)]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [M,terminalMean_final,terminalMean_initial,inner_sub_right,sub_mul]
  change _=(∫y,fderiv ℝ φ y ((centeringKernel hF x hr hl hT0 hT1 y).adjoint u) ∂μ)
  rw [←hEnds,←hFTC,hExchange]
  simp only [centeringKernel,ContinuousLinearMap.adjoint_adjoint]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

def primitiveExpectedField {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) : Point d :=
  ∫z,primitiveField F x r z ∂gibbs (primitivePotential F x r)

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

include hF hr hl hT0 hT1 in
lemma interpolation_norm_integrable : Integrable (fun y : Point d => ‖y‖) (interpolationLaw F x r T) := by
  have hlt : (lam:ℝ)*r^2<1 := by linarith only [hl]
  rw [interpolationLaw_eq_gibbs hF x hr.le hlt (by nlinarith [probability_time hT0 hT1])]
  simpa only [pow_one] using
    ((interpolationPotential_lowerTail hF x hr.le hlt hT0 hT1).hasExpMoments
      (interpolationPotential_smooth hF x hr.le hl hT0 hT1).continuous).hasMoments 1

include hlam in

theorem exists_actual_centering_flow {s a b : ℝ} (hs : 0<s) (hab : a≤b) :
    ∃Ψ : (Point d × Point d) → ℝ → (Point d × Point d),
      (∀p,Continuous (Ψ p) ∧ Ψ p a=p ∧ ∀t∈Icc a b,
        HasDerivWithinAt (Ψ p)
          (skewCenteringField (centeringKernel hF x hr hl hT0 hT1)
            (fun y => conditionalFieldMean F x r T y-primitiveExpectedField F x r) s (Ψ p t))
          (Icc a b) t) ∧
      (∀t∈Icc a b,Continuous (fun p => Ψ p t)) ∧
      (∀t∈Icc a b,((interpolationLaw F x r T).prod (stdGaussian (Point d))).map
        (fun p => Ψ p t)=(interpolationLaw F x r T).prod (stdGaussian (Point d))) := by
  let : IsProbabilityMeasure (interpolationLaw F x r T) :=
    interpolationLaw_probability hF x hr.le (by linarith only [hl]) T
  have hK := (centeringKernel_smooth hF x hr hlam hl hT0 hT1).of_le (by simp : (1:WithTop ℕ∞)≤(⊤:ℕ∞))
  have hM := (conditionalFieldMean_smooth hF x hr.le hl hT0 hT1).of_le (by simp : (1:WithTop ℕ∞)≤(⊤:ℕ∞))
  have hm : ContDiff ℝ 1 (fun y => conditionalFieldMean F x r T y-primitiveExpectedField F x r) :=
    hM.sub contDiff_const
  have hmL : LipschitzWith ⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩
      (fun y => conditionalFieldMean F x r T y-primitiveExpectedField F x r) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_sub_right] using
      (conditionalFieldMean_lipschitz hF x hr.le hl hT0 hT1).dist_le_mul y z
  exact exists_skew_centering_flow hK hm
    (by positivity : 0≤(Real.exp (Real.pi^2/4)*(Real.pi^2/2))*((lam:ℝ)*r))
    (centeringKernel_norm_le hF x hr hlam hl hT0 hT1) hmL
    (interpolation_norm_integrable hF x hr hl hT0 hT1)
    (fun u φ hφ hφc => centeringKernel_weak hF x hr hlam hl hT0 hT1 u hφ hφc) hs hab

include hlam in

theorem actual_centering_mean_law {s : ℝ} (hs : 0<s) :
    ∃Ψ : (Point d × Point d) → ℝ → (Point d × Point d),
      (∀p,Continuous (Ψ p) ∧ Ψ p 0=p ∧ ∀t∈Icc (0:ℝ) 1,
        HasDerivWithinAt (Ψ p)
          (skewCenteringField (centeringKernel hF x hr hl hT0 hT1)
            (fun y => conditionalFieldMean F x r T y-primitiveExpectedField F x r) s (Ψ p t))
          (Icc (0:ℝ) 1) t) ∧
      (∀t∈Icc (0:ℝ) 1,Continuous (fun p => Ψ p t)) ∧
      (∀t∈Icc (0:ℝ) 1,((interpolationLaw F x r T).prod (stdGaussian (Point d))).map
        (fun p => Ψ p t)=(interpolationLaw F x r T).prod (stdGaussian (Point d))) ∧
      ((interpolationLaw F x r T).prod (stdGaussian (Point d))).map
        (fun p => s • p.2+∫t in (0:ℝ)..1,conditionalFieldMean F x r T (Ψ p t).1)=
        (stdGaussian (Point d)).map (fun g => primitiveExpectedField F x r+s • g) := by
  let : IsProbabilityMeasure (interpolationLaw F x r T) :=
    interpolationLaw_probability hF x hr.le (by linarith only [hl]) T
  obtain ⟨Ψ,hΨ,hc,hlaw⟩ := exists_actual_centering_flow hF x hr hlam hl hT0 hT1 hs (by norm_num : (0:ℝ)≤1)
  refine ⟨Ψ,hΨ,hc,hlaw,?_⟩
  exact centering_output_law (conditionalFieldMean_smooth hF x hr.le hl hT0 hT1).continuous
    (primitiveExpectedField F x r) hs hΨ (hc 1 ⟨by norm_num,le_rfl⟩) (hlaw 1 ⟨by norm_num,le_rfl⟩)
end LogConcaveSampling

end

end

end

end OAI
