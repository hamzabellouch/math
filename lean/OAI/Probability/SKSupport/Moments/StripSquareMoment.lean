import Mathlib
import OAI.Probability.SKSupport.Foundations.RightGenerator
import OAI.Probability.SKSupport.Moments.SquareEquation

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def stripQ (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (t : ℝ) : ℝ :=
  ∫ ω, compactSquare W γ T t ((stripDrift W γ T).solution W.driver (Real.toNNReal t) ω) ∂W.law

def stripA (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (t : ℝ) : ℝ :=
  ∫ ω, (deriv (compactGradient W γ T t) ((stripDrift W γ T).solution W.driver (Real.toNNReal t) ω))^2 ∂W.law

lemma stripQ_continuous (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) :
    Continuous (stripQ W γ T) :=
  (stripDrift W γ T).expected_continuous W (compactSquare_family W γ T.property.1 T.property.2)
    (compactSquare_continuous W γ T.property.1 T.property.2)

lemma stripA_continuous (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) :
    Continuous (stripA W γ T) := by
  have hu := (compactGradient_family W γ T.property.1 T.property.2).deriv
  have hf : BoundedSmoothFamily (fun t x => (deriv (compactGradient W γ T t) x)^2) := by
    simpa only [pow_two] using hu.mul hu
  exact (stripDrift W γ T).expected_continuous W hf
    (compactCurvatureSquare_continuous W γ T.property.1 T.property.2)

lemma stripQ_zero (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) : stripQ W γ T 0 = 0 := by
  have hx (ω : Ω) : (stripDrift W γ T).solution W.driver 0 ω = 0 := by
    rw [(stripDrift W γ T).solution_eq _ W.driver_progressive]
    simp only [NNReal.coe_zero,intervalIntegral.integral_same,W.driver_zero,add_zero]
  have hu : compactGradient W γ T 0 0 = 0 := by
    rw [compactGradient,stripClamp_eq ⟨le_rfl,T.property.1⟩]
    exact gradient_zero W γ (by norm_num) (by norm_num)
  simp only [stripQ,Real.toNNReal_zero,hx,compactSquare,hu,mul_zero,integral_zero]

lemma stripQ_hasDerivWithinAt_right (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : Time) (s : ℝ≥0) (hsT : (s:ℝ) < T) :
    HasDerivWithinAt (stripQ W γ T) (stripA W γ T s) (Ioi (s:ℝ)) s := by
  let := W.isProbability
  let b := stripDrift W γ T
  have hf := compactSquare_family W γ T.property.1 T.property.2
  have hd := compactSquareRate_family W γ T.property.1 T.property.2
  have hgen := expected_hasDerivWithinAt_right W b hf hd
    (fun a c ha hac hc => compactSquare_integral_rate W γ T.property.1 T.property.2 ha hac hc)
    s hsT (compactSquareRate_right W γ T.property.1 T.property.2 (s:ℝ)) (stripDrift_pathDrift_right W γ T s)
  have hx := b.solution_measurable W s
  have hi1 : Integrable (fun ω => deriv (compactSquare W γ T s) (b.solution W.driver s ω)*b.pathDrift W s ω) W.law := by
    apply (integrable_family_comp hf.deriv (s:ℝ) hx).mul_bdd
    · exact ((b.pathDrift_measurable W).comp measurable_prodMk_left).aestronglyMeasurable
    · exact Eventually.of_forall (fun ω => b.pathDrift_bound W s ω)
  have hi2 := integrable_family_comp (P := W.law) hf.deriv.deriv (s:ℝ) hx
  have hi3 := integrable_family_comp (P := W.law) hd (s:ℝ) hx
  have he : (∫ ω, deriv (compactSquare W γ T s) (b.solution W.driver s ω)*b.pathDrift W s ω ∂W.law)+
      (1/2:ℝ)*(∫ ω, deriv (deriv (compactSquare W γ T s)) (b.solution W.driver s ω) ∂W.law)+
      (∫ ω, compactSquareRate W γ T s (b.solution W.driver s ω) ∂W.law) = stripA W γ T s := by
    have hi12 : Integrable (fun ω => deriv (compactSquare W γ T s) (b.solution W.driver s ω)*b.pathDrift W s ω+
        (1/2:ℝ)*deriv (deriv (compactSquare W γ T s)) (b.solution W.driver s ω)) W.law :=
      hi1.add (hi2.const_mul (1/2:ℝ))
    rw [← integral_const_mul,← integral_add hi1 (hi2.const_mul (1/2:ℝ)),← integral_add hi12 hi3]
    apply integral_congr_ae
    filter_upwards [] with ω
    simpa only [stripA,Real.toNNReal_coe,BoundedLipschitzDrift.pathDrift,b,stripDrift] using
      compactSquare_generator W γ T.property.1 T.property.2 (s:ℝ) (b.solution W.driver s ω)
  rw [he] at hgen
  exact hgen

theorem stripQ_eq_integral (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : Time) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    stripQ W γ T t = ∫ s in (0:ℝ)..t, stripA W γ T s := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht0
    (stripQ_continuous W γ T).continuousOn
    (fun s hs => by
      have hh := stripQ_hasDerivWithinAt_right W γ T (Real.toNNReal s)
        (by rw [Real.coe_toNNReal _ hs.1.le]; exact hs.2.trans_le htT)
      simpa only [Real.coe_toNNReal _ hs.1.le] using hh)
    ((stripA_continuous W γ T).intervalIntegrable 0 t)
  rw [stripQ_zero,sub_zero] at hi
  exact hi.symm

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

lemma diffusion_eq_strip (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    (s : ℝ≥0) (hs : (s:ℝ) ≤ T) (ω : Ω) :
    diffusion W γ s ω = (stripDrift W γ T).solution W.driver s ω := by
  have hs1 := hs.trans_lt T.property.2
  obtain ⟨n,hn⟩ := (eventually_le_diffusionHorizon hs1).exists
  rw [diffusion_eq_raw W γ s hs1,rawDiffusion_eq_local W γ n s hn]
  apply (stripDrift W γ (diffusionHorizonTime n)).solution_eq_of_agree
    (stripDrift W γ T) _ W.driver_progressive s _ s le_rfl ω
  intro r hr x
  have hrs : (r:ℝ) ≤ (s:ℝ) := hr
  rw [stripDrift_eq W γ _ ⟨r.coe_nonneg,hrs.trans hn⟩,
    stripDrift_eq W γ _ ⟨r.coe_nonneg,hrs.trans hs⟩]

def curvatureMoment (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ) : ℝ :=
  ∫ ω, (curvature W γ t (diffusion W γ (Real.toNNReal t) ω))^2 ∂W.law

lemma stripQ_eq_squareMoment (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) : stripQ W γ T t = squareMoment W γ (diffusion W γ) t := by
  have hs : ((Real.toNNReal t):ℝ) ≤ T := by rw [Real.coe_toNNReal _ ht.1]; exact ht.2
  unfold stripQ squareMoment
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [diffusion_eq_strip W γ T _ hs]
  simp only [compactSquare,compactGradient,stripClamp_eq ht,pow_two]

lemma stripA_eq_curvatureMoment (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) : stripA W γ T t = curvatureMoment W γ t := by
  have hs : ((Real.toNNReal t):ℝ) ≤ T := by rw [Real.coe_toNNReal _ ht.1]; exact ht.2
  have he : compactGradient W γ T t = gradient W γ t := by
    funext x
    simp only [compactGradient,stripClamp_eq ht]
  unfold stripA curvatureMoment
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [diffusion_eq_strip W γ T _ hs,he]
  rfl

theorem squareMoment_eq_integral_curvatureMoment (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    squareMoment W γ (diffusion W γ) t = ∫ s in (0:ℝ)..t, curvatureMoment W γ s := by
  let T : Time := ⟨t,⟨ht0,ht1⟩⟩
  rw [← stripQ_eq_squareMoment W γ T ⟨ht0,le_rfl⟩,stripQ_eq_integral W γ T ht0 le_rfl]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht0] at hs
  exact stripA_eq_curvatureMoment W γ T hs

lemma curvatureMoment_continuousOn (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) : ContinuousOn (curvatureMoment W γ) (Icc (0:ℝ) T) := by
  exact (stripA_continuous W γ ⟨T,⟨hT0,hT1⟩⟩).continuousOn.congr
    (fun t ht => (stripA_eq_curvatureMoment W γ ⟨T,⟨hT0,hT1⟩⟩ ht).symm)

lemma squareMoment_zero (W : BrownianSystem Ω) (γ : OrderParameter) :
    squareMoment W γ (diffusion W γ) 0 = 0 := by
  rw [squareMoment_eq_integral_curvatureMoment W γ (by norm_num) (by norm_num),intervalIntegral.integral_same]

theorem squareMoment_hasDerivWithinAt (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasDerivWithinAt (squareMoment W γ (diffusion W γ)) (curvatureMoment W γ t) (Ici (0:ℝ)) t := by
  let T : Time := ⟨(t+1)/2,⟨by linarith,by linarith⟩⟩
  have htt : t < (T:ℝ) := by dsimp [T]; linarith
  have hc := stripA_continuous W γ T
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  rw [stripA_eq_curvatureMoment W γ T ⟨ht0,htt.le⟩] at hd
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htt)] with s hs hsT
    rw [← stripQ_eq_squareMoment W γ T ⟨hs,hsT.le⟩,stripQ_eq_integral W γ T hs hsT.le]
  · rw [← stripQ_eq_squareMoment W γ T ⟨ht0,htt.le⟩,stripQ_eq_integral W γ T ht0 htt.le]

end ZeroTemperatureSK

end
end

end OAI
