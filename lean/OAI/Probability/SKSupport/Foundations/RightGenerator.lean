import Mathlib
import OAI.Probability.SKSupport.Diffusion.BoundedDiffusionProperties

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat
variable {Ω : Type*} [MeasurableSpace Ω]

theorem expected_hasDerivWithinAt_right (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    {F D : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) (hD : BoundedSmoothFamily D)
    {T : ℝ} (he : ∀ a c, 0 ≤ a → a ≤ c → c ≤ T → ∀ x,
      F c x-F a x = ∫ r in a..c, D r x)
    (s : ℝ≥0) (hsT : (s:ℝ) < T)
    (hDr : ∀ x, ContinuousWithinAt (fun r => D r x) (Ioi (s:ℝ)) s)
    (hbr : ∀ᵐ ω ∂W.law, ContinuousWithinAt (fun r => b.pathDrift W r ω) (Ioi (s:ℝ)) s) :
    HasDerivWithinAt
      (fun t : ℝ => ∫ ω, F t (b.solution W.driver (Real.toNNReal t) ω) ∂W.law)
      ((∫ ω, deriv (F s) (b.solution W.driver s ω)*b.pathDrift W s ω ∂W.law)+
        (1/2:ℝ)*(∫ ω, deriv (deriv (F s)) (b.solution W.driver s ω) ∂W.law)+
        (∫ ω, D s (b.solution W.driver s ω) ∂W.law)) (Ioi (s:ℝ)) s := by
  let := W.isProbability
  let Y := b.solution W.driver s
  have hYm : Measurable Y := b.solution_measurable W s
  obtain ⟨C₁,hC₁⟩ := hF.deriv.bound
  obtain ⟨C₂,hC₂⟩ := hF.deriv.deriv.bound
  obtain ⟨C₃,hC₃⟩ := hF.bounds 3
  obtain ⟨Ct,hCt⟩ := hD.bound
  obtain ⟨L,hL⟩ := BoundedSmoothFamily_lipschitz hD
  let Q (t : ℝ) := ∫ ω, F t (b.solution W.driver (Real.toNNReal t) ω) ∂W.law
  let H : ℝ := ∫ ω, deriv (deriv (F s)) (Y ω) ∂W.law
  let A (t : ℝ) := ∫ ω, deriv (F s) (Y ω)*b.displacement W s t ω ∂W.law
  let J (t : ℝ) := ∫ ω, (∫ r in (s:ℝ)..t, D r (Y ω)) ∂W.law
  let K (t : ℝ) := A t/(t-s)+(1/2:ℝ)*H+J t/(t-s)
  have hcoeff : Measurable (fun ω => deriv (F s) (Y ω)) :=
    ((hF.deriv.regular s).smooth.continuous.measurable).comp hYm
  have hma : Measurable (fun p : ℝ × Ω => deriv (F s) (Y p.2)*b.pathDrift W p.1 p.2) :=
    (hcoeff.comp measurable_snd).mul (b.pathDrift_measurable W)
  have halim := expected_time_average_tendsto_right (P := W.law) hma
    (mul_nonneg C₁.coe_nonneg b.bound.coe_nonneg)
    (fun r ω => by
      rw [abs_mul]
      exact mul_le_mul (hC₁ s (Y ω)) (b.pathDrift_bound W r ω) (abs_nonneg _) C₁.coe_nonneg)
    (s:ℝ) (by
      filter_upwards [hbr] with ω hω
      exact continuousWithinAt_const.mul hω)
  have hAlim : Tendsto (fun t => A t/(t-s)) (𝓝[>] (s:ℝ))
      (𝓝 (∫ ω, deriv (F s) (Y ω)*b.pathDrift W s ω ∂W.law)) := by
    convert halim using 1
    funext t
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [intervalIntegral.integral_const_mul]
    rfl
  have hmj : Measurable (fun p : ℝ × Ω => D p.1 (Y p.2)) :=
    hD.measurable.comp (measurable_fst.prodMk (hYm.comp measurable_snd))
  have hjlim := expected_time_average_tendsto_right (P := W.law) hmj Ct.coe_nonneg
    (fun r ω => hCt r (Y ω)) (s:ℝ) (Eventually.of_forall (fun ω => hDr (Y ω)))
  have hJlim : Tendsto (fun t => J t/(t-s)) (𝓝[>] (s:ℝ))
      (𝓝 (∫ ω, D s (Y ω) ∂W.law)) := by
    convert hjlim using 1
    funext t
    exact (integral_div (t-(s:ℝ)) _).symm
  have hKlim := (hAlim.add_const ((1/2:ℝ)*H)).add hJlim
  let E (t : ℝ) := (C₃:ℝ)/6*(Real.sqrt (t-s)*normalThirdMoment)+
    (C₂:ℝ)*(b.bound:ℝ)*(Real.sqrt (t-s)*normalFirstMoment+(b.bound:ℝ)*(t-s))+
    (L:ℝ)*(Real.sqrt (t-s)*normalFirstMoment+(b.bound:ℝ)*(t-s))
  have hzero : Tendsto (fun t : ℝ => t-(s:ℝ)) (𝓝[>] (s:ℝ)) (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ => t) (𝓝[>] (s:ℝ)) (𝓝 (s:ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_self] using hh.sub_const (s:ℝ)
  have hsqrt := hzero.sqrt
  have hElim : Tendsto E (𝓝[>] (s:ℝ)) (𝓝 0) := by
    have hbase := (hsqrt.mul_const normalFirstMoment).add (hzero.const_mul (b.bound:ℝ))
    simpa only [E,Real.sqrt_zero,zero_mul,mul_zero,add_zero] using
      (((hsqrt.mul_const normalThirdMoment).const_mul ((C₃:ℝ)/6)).add
        (hbase.const_mul ((C₂:ℝ)*(b.bound:ℝ)))).add (hbase.const_mul (L:ℝ))
  have hbound : ∀ᶠ t in 𝓝[>] (s:ℝ), |slope Q s t-K t| ≤ E t := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hsT)] with t hst htT
    have hp : 0 < t-(s:ℝ) := sub_pos.mpr hst
    let h := Real.toNNReal (t-(s:ℝ))
    have hcoe : (h:ℝ)=t-(s:ℝ) := Real.coe_toNNReal _ hp.le
    have htime : (s:ℝ)+(h:ℝ)=t := by rw [hcoe]; ring
    have hnn : s+h=Real.toNNReal t := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add,htime,Real.coe_toNNReal _ (s.coe_nonneg.trans hst.le)]
    have hstep := expected_integral_time_step W.brownian.toIsPreBrownianReal W.measurable s h
      (b.solution_adapted W s) (b.solution_integrable W s)
      (b.displacement_measurable W s (s+h)) b.bound
      (fun ω => by
        have hb := b.displacement_bound W (s:ℝ) ((s+h:ℝ≥0):ℝ) ω
        simpa only [NNReal.coe_add,add_sub_cancel_left,abs_of_nonneg h.coe_nonneg] using hb)
      hF hD C₁ C₂ C₃ L (hC₁ s) (hC₂ s) (hC₃ s) hL
      (he s ((s:ℝ)+(h:ℝ)) s.coe_nonneg (by linarith [h.coe_nonneg]) (by rw [htime]; exact htT.le))
    have hsol : (∫ ω, F ((s:ℝ)+(h:ℝ))
        (b.solution W.driver s ω+(W.B (s+h) ω-W.B s ω)+b.displacement W s (s+h) ω) ∂W.law) = Q t := by
      unfold Q
      apply integral_congr_ae
      filter_upwards [b.solution_increment W s h] with ω hω
      rw [← hω,hnn,htime]
    rw [hsol] at hstep
    have hqs : (∫ ω, F s (b.solution W.driver s ω) ∂W.law) = Q s := by simp only [Q,Real.toNNReal_coe]
    rw [hqs] at hstep
    have hat : (∫ ω, deriv (F s) (b.solution W.driver s ω)*b.displacement W s (s+h) ω ∂W.law) = A t := by
      simp only [A,Y,htime]
    rw [hat,htime,hcoe] at hstep
    change |Q t-Q s-A t-(t-(s:ℝ))/2*H-J t| ≤ _ at hstep
    have heq : slope Q s t-K t = (Q t-Q s-A t-(t-(s:ℝ))/2*H-J t)/(t-s) := by
      rw [slope_def_field]
      dsimp only [K]
      field_simp
      ring
    rw [heq,abs_div,abs_of_pos hp,div_le_iff₀ hp]
    convert hstep using 1
    all_goals try dsimp only [E]
    all_goals first | rfl | ring
  have herr : Tendsto (fun t => slope Q s t-K t) (𝓝[>] (s:ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) _ hElim
    simpa only [Real.norm_eq_abs] using hbound
  have hh := herr.add hKlim
  apply (hasDerivWithinAt_iff_tendsto_slope' (show (s:ℝ) ∉ Ioi (s:ℝ) by simp)).mpr
  convert hh using 1
  · funext t
    dsimp only [K] at *
    ring
  · simp only [zero_add,H,Y]

end ZeroTemperatureSK

end
end

end OAI
