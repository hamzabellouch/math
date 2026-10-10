import Mathlib
import OAI.Probability.SKSupport.Backward.TiltedBackward
import OAI.Probability.SKSupport.Foundations.RightGenerator

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma Heat.varianceGradient_joint_continuous {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) :
    Continuous (fun p : ℝ × ℝ => deriv (varianceLogHeat c p.1 f) p.2) := by
  have he : (fun p : ℝ × ℝ => deriv (varianceLogHeat c p.1 f) p.2)=
      fun p => varianceTilted c p.1 f (deriv f) p.2 :=
    funext (fun p => congrFun (deriv_varianceLogHeat_tilted hf hLip hc p.1) p.2)
  rw [he]
  exact varianceTilted_joint_continuous hf hLip hf.deriv_bounded hc

lemma Heat.tiltedBackwardRate_continuous {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    Continuous (fun p : ℝ × ℝ => tiltedBackwardRate c T f g p.1 p.2) := by
  have hU := varianceTilted_family hf hLip hg hc
  have hUc := varianceTilted_joint_continuous hf hLip hg hc
  have hUx := hU.continuous_iteratedDeriv hUc 1
  have hUxx := hU.continuous_iteratedDeriv hUc 2
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hUx hUxx
  have hr : Continuous (fun p : ℝ × ℝ => tiltedRate c f g p.1 p.2) :=
    (continuous_const.mul hUxx).add
      ((continuous_const.mul (varianceGradient_joint_continuous hf hLip hc)).mul hUx)
  change Continuous (fun p : ℝ × ℝ => -tiltedRate c f g (T-p.1) p.2)
  exact hr.neg.comp (f := fun p : ℝ × ℝ => (T-p.1,p.2))
    ((continuous_const.sub continuous_fst).prodMk continuous_snd)

lemma drift_tilted_path_continuous_right (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : RegularDatum f) (hLip : LipschitzWith K f)
    {c a T : ℝ} (hc : 0 ≤ c)
    (hmatch : ∀ t ∈ Ico a T, ∀ x, b.f t x=c*deriv (varianceLogHeat c (T-t) f) x)
    (s : ℝ≥0) (has : a ≤ s) (hsT : (s:ℝ) < T) :
    ∀ᵐ ω ∂W.law, ContinuousWithinAt (fun r => b.pathDrift W r ω) (Ioi (s:ℝ)) s := by
  filter_upwards [b.solution_continuous_ae W] with ω hω
  have hβ : Continuous (fun t : ℝ => c*deriv (varianceLogHeat c (T-t) f)
      (b.solution W.driver (Real.toNNReal t) ω)) :=
    continuous_const.mul ((varianceGradient_joint_continuous hf hLip hc).comp
      ((continuous_const.sub continuous_id).prodMk (hω.comp (by fun_prop : Continuous Real.toNNReal))))
  apply hβ.continuousWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hsT)] with r hr hrT
    unfold BoundedLipschitzDrift.pathDrift
    rw [Real.coe_toNNReal _ (s.coe_nonneg.trans hr.le)]
    exact hmatch r ⟨has.trans hr.le,hrT⟩ _
  · unfold BoundedLipschitzDrift.pathDrift
    rw [Real.toNNReal_coe]
    exact hmatch s ⟨has,hsT⟩ _

theorem expected_tiltedBackward_right_zero (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    {f g : ℝ → ℝ} {K : ℝ≥0} (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c a T : ℝ} (hc : 0 ≤ c)
    (hmatch : ∀ t ∈ Ico a T, ∀ x, b.f t x=c*deriv (varianceLogHeat c (T-t) f) x)
    (s : ℝ≥0) (has : a ≤ s) (hsT : (s:ℝ) < T) :
    HasDerivWithinAt (fun t : ℝ => ∫ ω, tiltedBackward c T f g t
      (b.solution W.driver (Real.toNNReal t) ω) ∂W.law) 0 (Ioi (s:ℝ)) s := by
  let := W.isProbability
  have hF := tiltedBackward_family hf hLip hg hc T
  have hD := tiltedBackwardRate_family hf hLip hg hc T
  have hgen := expected_hasDerivWithinAt_right W b hF hD
    (fun a d ha had hd => tiltedBackward_integrated_rate hf hLip hg hc ha had hd)
    s hsT (fun x => ((tiltedBackwardRate_continuous hf hLip hg hc T).comp
      (continuous_id.prodMk continuous_const)).continuousWithinAt)
    (drift_tilted_path_continuous_right W b hf hLip hc hmatch s has hsT)
  have hx := b.solution_measurable W s
  have hi1 : Integrable (fun ω => deriv (tiltedBackward c T f g s) (b.solution W.driver s ω)*b.pathDrift W s ω) W.law := by
    apply (integrable_family_comp hF.deriv (s:ℝ) hx).mul_bdd
    · exact ((b.pathDrift_measurable W).comp measurable_prodMk_left).aestronglyMeasurable
    · exact Eventually.of_forall (fun ω => b.pathDrift_bound W s ω)
  have hi2 := integrable_family_comp (P := W.law) hF.deriv.deriv (s:ℝ) hx
  have hi3 := integrable_family_comp (P := W.law) hD (s:ℝ) hx
  have he : (∫ ω, deriv (tiltedBackward c T f g s) (b.solution W.driver s ω)*b.pathDrift W s ω ∂W.law)+
      (1/2:ℝ)*(∫ ω, deriv (deriv (tiltedBackward c T f g s)) (b.solution W.driver s ω) ∂W.law)+
      (∫ ω, tiltedBackwardRate c T f g s (b.solution W.driver s ω) ∂W.law)=0 := by
    have hsum := integral_add (hi1.add (hi2.const_mul (1/2:ℝ))) hi3
    dsimp only [Pi.add_apply] at hsum
    rw [← integral_const_mul,← integral_add hi1 (hi2.const_mul (1/2:ℝ)),← hsum]
    have hz : (fun ω => deriv (tiltedBackward c T f g s) (b.solution W.driver s ω)*b.pathDrift W s ω+
        (1/2:ℝ)*deriv (deriv (tiltedBackward c T f g s)) (b.solution W.driver s ω)+
        tiltedBackwardRate c T f g s (b.solution W.driver s ω))=fun _ => 0 := by
      funext ω
      unfold tiltedBackward
      simp only [BoundedLipschitzDrift.pathDrift,Real.toNNReal_coe,
        hmatch s ⟨has,hsT⟩,tiltedBackwardRate,tiltedRate]
      ring
    rw [hz,integral_zero]
  rwa [he] at hgen

theorem expected_transition_tiltedMean (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    {f g : ℝ → ℝ} {K : ℝ≥0} (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) {a T : ℝ≥0} (haT : a ≤ T)
    (hmatch : ∀ t ∈ Ico (a:ℝ) T, ∀ x, b.f t x=c*deriv (varianceLogHeat c (T-t) f) x) :
    (∫ ω, g (b.solution W.driver T ω) ∂W.law)=
      ∫ ω, varianceTilted c ((T:ℝ)-a) f g (b.solution W.driver a ω) ∂W.law := by
  have hcF : Continuous (fun r : ℝ =>
      ∫ ω, tiltedBackward c T f g r (b.solution W.driver (Real.toNNReal r) ω) ∂W.law) := by
    let := W.isProbability
    have hF := tiltedBackward_family hf hLip hg hc T
    obtain ⟨C,hC⟩ := hF.bound
    apply continuous_of_dominated (bound := fun _ => (C:ℝ))
    · intro r
      exact ((hF.regular r).smooth.continuous.measurable.comp
        (b.solution_measurable W (Real.toNNReal r))).aestronglyMeasurable
    · intro r
      exact Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs] using hC r (b.solution W.driver (Real.toNNReal r) ω))
    · exact integrable_const _
    · filter_upwards [b.solution_continuous_ae W] with ω hω
      exact (tiltedBackward_continuous hf hLip hg hc T).comp
        (continuous_id.prodMk (hω.comp (by fun_prop : Continuous Real.toNNReal)))
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (show (a:ℝ) ≤ T from haT)
    hcF.continuousOn (f' := fun _ => (0:ℝ)) (fun r hr => by
      have hh := expected_tiltedBackward_right_zero W b hf hLip hg hc hmatch (Real.toNNReal r)
        (by rw [Real.coe_toNNReal _ (a.coe_nonneg.trans hr.1.le)];exact hr.1.le)
        (by rw [Real.coe_toNNReal _ (a.coe_nonneg.trans hr.1.le)];exact hr.2)
      simpa only [Real.coe_toNNReal _ (a.coe_nonneg.trans hr.1.le)] using hh)
    (intervalIntegrable_const)
  simp only [intervalIntegral.integral_zero,Real.toNNReal_coe,tiltedBackward_terminal] at hi
  exact sub_eq_zero.mp hi.symm

end ZeroTemperatureSK

end
end

end OAI
