import Mathlib
import OAI.Probability.SKSupport.Diffusion.BoundedDiffusionProperties
import OAI.Probability.SKSupport.Regularity.RightRegularity

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactValueRate_eq (W : BrownianSystem Ω) (γ : OrderParameter) (T t x : ℝ) :
    compactValueRate W γ T t x = -(1/2:ℝ)*deriv (compactGradient W γ T t) x-
      (1/2:ℝ)*compactCoeff γ T t*(compactGradient W γ T t x)^2 := rfl

lemma compactGradient_hasDerivWithinAt_right (W : BrownianSystem Ω) (γ : OrderParameter)
    {T t : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (ht0 : 0 ≤ t) (htT : t < T) (x : ℝ) :
    HasDerivWithinAt (fun s => compactGradient W γ T s x)
      (deriv (compactValueRate W γ T t) x) (Ioi t) t := by
  have hh := value_derivative_hasDerivWithinAt_right W γ hT0 hT1 ht0 htT 1 x
  simp only [iteratedDeriv_one] at hh
  apply hh.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htT)] with s hs hsT
    simp only [compactGradient,stripClamp_eq ⟨ht0.trans hs.le,hsT.le⟩,gradient]
  · simp only [compactGradient,stripClamp_eq ⟨ht0,htT.le⟩,gradient]

lemma deriv_compactValueRate (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    deriv (compactValueRate W γ T t) x =
      -(1/2:ℝ)*deriv (deriv (compactGradient W γ T t)) x-
      compactCoeff γ T t*compactGradient W γ T t x*deriv (compactGradient W γ T t) x := by
  have hu := compactGradient_family W γ hT0 hT1
  have hd := ((hu.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hdd := ((hu.deriv.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hh := (hdd.const_mul (-(1/2:ℝ))).sub ((hd.pow 2).const_mul ((1/2:ℝ)*compactCoeff γ T t))
  have he : (compactValueRate W γ T t) = (fun x =>
      -(1/2:ℝ)*deriv (compactGradient W γ T t) x-(1/2:ℝ)*compactCoeff γ T t*(compactGradient W γ T t x)^2) :=
    funext (compactValueRate_eq W γ T t)
  rw [he]
  calc
    _ = _ := hh.deriv
    _ = _ := by ring

def compactSquare (W : BrownianSystem Ω) (γ : OrderParameter) (T t x : ℝ) : ℝ :=
  compactGradient W γ T t x*compactGradient W γ T t x

def compactSquareRate (W : BrownianSystem Ω) (γ : OrderParameter) (T t x : ℝ) : ℝ :=
  2*compactGradient W γ T t x*deriv (compactValueRate W γ T t) x

lemma compactSquare_family (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) : BoundedSmoothFamily (compactSquare W γ T) :=
  (compactGradient_family W γ hT0 hT1).mul (compactGradient_family W γ hT0 hT1)

lemma compactSquareRate_family (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) : BoundedSmoothFamily (compactSquareRate W γ T) :=
  ((compactGradient_family W γ hT0 hT1).const_mul 2).mul
    (compactValueRate_family W γ hT0 hT1).deriv

lemma compactSquareRate_right (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    ContinuousWithinAt (fun s => compactSquareRate W γ T s x) (Ioi t) t := by
  have hu := compactGradient_rightSmooth W γ hT0 hT1 0 t x
  have hD := compactValueRate_rightSmooth W γ hT0 hT1 1 t x
  simp only [iteratedDeriv_zero,iteratedDeriv_one] at hu hD
  exact ((continuousWithinAt_const.mul hu).mul hD).mono Ioi_subset_Ici_self

lemma compactSquare_integral_rate (W : BrownianSystem Ω) (γ : OrderParameter)
    {T a b : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (x : ℝ) :
    compactSquare W γ T b x-compactSquare W γ T a x =
      ∫ r in a..b, compactSquareRate W γ T r x := by
  apply (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab _ _
    ((compactSquareRate_family W γ hT0 hT1).intervalIntegrable x a b)).symm
  · have hc : Continuous (fun t => compactGradient W γ T t x) :=
      (compactGradient_continuous W γ hT0 hT1).comp
        (continuous_id.prodMk continuous_const)
    exact (hc.mul hc).continuousOn
  · intro t ht
    have hd := compactGradient_hasDerivWithinAt_right W γ hT0 hT1 (ha.trans ht.1.le) (ht.2.trans_le hb) x
    convert hd.mul hd using 1 <;> (try rfl)
    dsimp only [compactSquareRate]
    ring

lemma compactSquare_generator (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    deriv (compactSquare W γ T t) x*compactDrift W γ T t x+
      (1/2:ℝ)*deriv (deriv (compactSquare W γ T t)) x+compactSquareRate W γ T t x =
      (deriv (compactGradient W γ T t) x)^2 := by
  have hu := compactGradient_family W γ hT0 hT1
  have hd (x : ℝ) := ((hu.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hdd (x : ℝ) := ((hu.deriv.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have he (x : ℝ) : deriv (compactSquare W γ T t) x =
      deriv (compactGradient W γ T t) x*compactGradient W γ T t x+
        compactGradient W γ T t x*deriv (compactGradient W γ T t) x := (hd x |>.mul (hd x)).deriv
  have he2 : deriv (compactSquare W γ T t) = fun x =>
      deriv (compactGradient W γ T t) x*compactGradient W γ T t x+
        compactGradient W γ T t x*deriv (compactGradient W γ T t) x := funext he
  have hh := ((hdd x |>.mul (hd x)).add ((hd x).mul (hdd x))).deriv
  change deriv (fun y => deriv (compactGradient W γ T t) y*compactGradient W γ T t y+
    compactGradient W γ T t y*deriv (compactGradient W γ T t) y) x = _ at hh
  rw [he,he2,hh]
  unfold compactDrift compactSquareRate
  rw [deriv_compactValueRate W γ hT0 hT1]
  ring

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

lemma compactGradient_derivative_continuous (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => iteratedDeriv n (compactGradient W γ T p.1) p.2) := by
  change Continuous (fun p : ℝ × ℝ => iteratedDeriv n (deriv (value W γ (stripClamp T p.1))) p.2)
  simp only [← iteratedDeriv_succ']
  have hc := value_derivative_continuousOn W γ hT0 hT1 (n+1)
  have hg : ContinuousOn (fun p : ℝ × ℝ => (stripClamp T p.1,p.2)) univ :=
    (((continuous_stripClamp T).comp continuous_fst).prodMk continuous_snd).continuousOn
  have hm : MapsTo (fun p : ℝ × ℝ => (stripClamp T p.1,p.2)) univ
      (Icc (0:ℝ) T ×ˢ (univ : Set ℝ)) := fun p _ => ⟨stripClamp_mem hT0 p.1,mem_univ _⟩
  exact continuousOn_univ.mp (ContinuousOn.comp
    (f := fun p : ℝ × ℝ => (stripClamp T p.1,p.2))
    (g := fun p : ℝ × ℝ => iteratedDeriv (n+1) (value W γ p.1) p.2) hc hg hm)

lemma BoundedLipschitzDrift.expected_continuous (b : BoundedLipschitzDrift)
    (W : BrownianSystem Ω) {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F)
    (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) :
    Continuous (fun r : ℝ => ∫ ω, F r (b.solution W.driver (Real.toNNReal r) ω) ∂W.law) := by
  let := W.isProbability
  obtain ⟨C,hC⟩ := hF.bound
  apply continuous_of_dominated (bound := fun _ => (C:ℝ))
  · intro r
    exact ((hF.regular r).smooth.continuous.measurable.comp
      (b.solution_measurable W (Real.toNNReal r))).aestronglyMeasurable
  · intro r
    exact Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hC r (b.solution W.driver (Real.toNNReal r) ω))
  · exact integrable_const _
  · filter_upwards [b.solution_continuous_ae W] with ω hω
    exact hc.comp (continuous_id.prodMk (hω.comp (by fun_prop : Continuous Real.toNNReal)))

lemma stripDrift_pathDrift_right (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : Time) (s : ℝ≥0) :
    ∀ᵐ ω ∂W.law, ContinuousWithinAt (fun r => (stripDrift W γ T).pathDrift W r ω) (Ioi (s:ℝ)) s := by
  filter_upwards [(stripDrift W γ T).solution_continuous_ae W] with ω hω
  have hx : Continuous (fun r : ℝ => (stripDrift W γ T).solution W.driver (Real.toNNReal r) ω) :=
    hω.comp (by fun_prop : Continuous Real.toNNReal)
  have hu : Continuous (fun r : ℝ => compactGradient W γ T r
      ((stripDrift W γ T).solution W.driver (Real.toNNReal r) ω)) :=
    (compactGradient_continuous W γ T.property.1 T.property.2).comp (continuous_id.prodMk hx)
  have hh := ((compactCoeff_rightContinuous γ T.property.1 T.property.2 (s:ℝ)).mono Ioi_subset_Ici_self).mul hu.continuousWithinAt
  apply hh.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [BoundedLipschitzDrift.pathDrift,stripDrift,compactDrift,
      Real.coe_toNNReal _ (s.coe_nonneg.trans hr.le),Pi.mul_apply]
  · simp only [BoundedLipschitzDrift.pathDrift,stripDrift,compactDrift,Real.toNNReal_coe,Pi.mul_apply]

lemma compactSquare_continuous (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Continuous (fun p : ℝ × ℝ => compactSquare W γ T p.1 p.2) :=
  (compactGradient_continuous W γ hT0 hT1).mul (compactGradient_continuous W γ hT0 hT1)

lemma compactCurvatureSquare_continuous (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Continuous (fun p : ℝ × ℝ => (deriv (compactGradient W γ T p.1) p.2)^2) := by
  have hh := compactGradient_derivative_continuous W γ hT0 hT1 1
  simp only [iteratedDeriv_one] at hh
  exact hh.pow 2

end ZeroTemperatureSK

end
end

end OAI
