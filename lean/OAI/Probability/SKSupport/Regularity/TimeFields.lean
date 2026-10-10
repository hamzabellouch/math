import Mathlib
import OAI.Probability.SKSupport.Foundations.RightGenerator

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto

structure TimeField (T : ℝ) where
  f : ℝ → ℝ → ℝ
  d : ℝ → ℝ → ℝ
  smooth : BoundedSmoothFamily f
  rate_smooth : BoundedSmoothFamily d
  continuous : Continuous (fun p : ℝ × ℝ => f p.1 p.2)
  rate_right : ∀ t x, ContinuousWithinAt (fun s => d s x) (Ioi t) t
  time_deriv : ∀ t, 0 ≤ t → t < T → ∀ x,
    HasDerivWithinAt (fun s => f s x) (d t x) (Ioi t) t

namespace TimeField
variable {T : ℝ}

def add (F G : TimeField T) : TimeField T where
  f := fun t x => F.f t x+G.f t x
  d := fun t x => F.d t x+G.d t x
  smooth := F.smooth.add G.smooth
  rate_smooth := F.rate_smooth.add G.rate_smooth
  continuous := F.continuous.add G.continuous
  rate_right := fun t x => (F.rate_right t x).add (G.rate_right t x)
  time_deriv := fun t ht hT x => (F.time_deriv t ht hT x).add (G.time_deriv t ht hT x)

def const_mul (c : ℝ) (F : TimeField T) : TimeField T where
  f := fun t x => c*F.f t x
  d := fun t x => c*F.d t x
  smooth := F.smooth.const_mul c
  rate_smooth := F.rate_smooth.const_mul c
  continuous := continuous_const.mul F.continuous
  rate_right := fun t x => continuousWithinAt_const.mul (F.rate_right t x)
  time_deriv := fun t ht hT x => (F.time_deriv t ht hT x).const_mul c

def mul (F G : TimeField T) : TimeField T where
  f := fun t x => F.f t x*G.f t x
  d := fun t x => F.d t x*G.f t x+F.f t x*G.d t x
  smooth := F.smooth.mul G.smooth
  rate_smooth := (F.rate_smooth.mul G.smooth).add (F.smooth.mul G.rate_smooth)
  continuous := F.continuous.mul G.continuous
  rate_right := fun t x => ((F.rate_right t x).mul
    ((G.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt.continuousWithinAt)).add
    (((F.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt.continuousWithinAt).mul (G.rate_right t x))
  time_deriv := fun t ht hT x => (F.time_deriv t ht hT x).mul (G.time_deriv t ht hT x)

lemma integral_rate (F : TimeField T) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (x : ℝ) :
    F.f b x-F.f a x=∫ t in a..b, F.d t x := by
  apply (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab _ _
    (F.rate_smooth.intervalIntegrable x a b)).symm
  · exact (F.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
  · intro t ht
    exact F.time_deriv t (ha.trans ht.1.le) (ht.2.trans_le hb) x

def generator (F : TimeField T) (b : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (F.f t) x*b t x+(1/2:ℝ)*deriv (deriv (F.f t)) x+F.d t x

lemma generator_add (F G : TimeField T) (b : ℝ → ℝ → ℝ) (t x : ℝ) :
    (F.add G).generator b t x=F.generator b t x+G.generator b t x := by
  have hF (x : ℝ) := ((F.smooth.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hG (x : ℝ) := ((G.smooth.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hFd (x : ℝ) := ((F.smooth.deriv.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hGd (x : ℝ) := ((G.smooth.deriv.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have he : deriv (fun y => F.f t y+G.f t y)=fun y => deriv (F.f t) y+deriv (G.f t) y :=
    funext (fun y => ((hF y).add (hG y)).deriv)
  dsimp only [generator,add]
  have hd := ((hFd x).add (hGd x)).deriv
  change deriv (fun y => deriv (F.f t) y+deriv (G.f t) y) x = _ at hd
  rw [he,hd]
  ring

lemma generator_const_mul (F : TimeField T) (c : ℝ) (b : ℝ → ℝ → ℝ) (t x : ℝ) :
    (F.const_mul c).generator b t x=c*F.generator b t x := by
  have hF (x : ℝ) := ((F.smooth.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hFd (x : ℝ) := ((F.smooth.deriv.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have he : deriv (fun y => c*F.f t y)=fun y => c*deriv (F.f t) y :=
    funext (fun y => ((hF y).const_mul c).deriv)
  dsimp only [generator,const_mul]
  rw [he,((hFd x).const_mul c).deriv]
  ring

lemma generator_mul (F G : TimeField T) (b : ℝ → ℝ → ℝ) (t x : ℝ) :
    (F.mul G).generator b t x=F.f t x*G.generator b t x+G.f t x*F.generator b t x+
      deriv (F.f t) x*deriv (G.f t) x := by
  have hF (x : ℝ) := ((F.smooth.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hG (x : ℝ) := ((G.smooth.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hFd (x : ℝ) := ((F.smooth.deriv.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hGd (x : ℝ) := ((G.smooth.deriv.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have he : deriv (fun y => F.f t y*G.f t y)=fun y => deriv (F.f t) y*G.f t y+F.f t y*deriv (G.f t) y :=
    funext (fun y => ((hF y).mul (hG y)).deriv)
  have hd := (((hFd x).mul (hG x)).add ((hF x).mul (hGd x))).deriv
  change deriv (fun y => deriv (F.f t) y*G.f t y+F.f t y*deriv (G.f t) y) x = _ at hd
  dsimp only [generator,mul]
  rw [he,hd]
  ring

variable {Ω : Type*} [MeasurableSpace Ω]

def expected (F : TimeField T) (b : BoundedLipschitzDrift) (W : BrownianSystem Ω) (t : ℝ) : ℝ :=
  ∫ ξ, F.f t (b.solution W.driver (Real.toNNReal t) ξ) ∂W.law

lemma expected_continuous (F : TimeField T) (b : BoundedLipschitzDrift) (W : BrownianSystem Ω) :
    Continuous (F.expected b W) := by
  let := W.isProbability
  obtain ⟨bound,hbound⟩ := F.smooth.bound
  apply continuous_of_dominated (bound := fun _ => (bound:ℝ))
  · intro time
    exact (integrable_family_comp F.smooth time (b.solution_measurable W _)).aestronglyMeasurable
  · intro time
    exact Eventually.of_forall (fun sample => by
      simpa only [Real.norm_eq_abs] using
        hbound time (b.solution W.driver (Real.toNNReal time) sample))
  · exact integrable_const _
  · filter_upwards [b.solution_continuous_ae W] with sample hsample
    exact F.continuous.comp (continuous_id.prodMk (hsample.comp continuous_real_toNNReal))

lemma expected_hasDerivWithinAt_right (F : TimeField T) (b : BoundedLipschitzDrift) (W : BrownianSystem Ω)
    (s : ℝ≥0) (hs : (s:ℝ) < T)
    (hbr : ∀ᵐ ξ ∂W.law, ContinuousWithinAt (fun r => b.pathDrift W r ξ) (Ioi (s:ℝ)) s) :
    HasDerivWithinAt (F.expected b W)
      (∫ ξ, F.generator b.f s (b.solution W.driver s ξ) ∂W.law) (Ioi (s:ℝ)) s := by
  let := W.isProbability
  have hd := ZeroTemperatureSK.expected_hasDerivWithinAt_right W b F.smooth F.rate_smooth
    (fun a c ha hac hc x => F.integral_rate ha hac hc x) s hs (F.rate_right s) hbr
  have hx := b.solution_measurable W s
  have hi1 : Integrable (fun ξ => deriv (F.f s) (b.solution W.driver s ξ)*b.pathDrift W s ξ) W.law := by
    apply (integrable_family_comp F.smooth.deriv (s:ℝ) hx).mul_bdd
    · exact ((b.pathDrift_measurable W).comp measurable_prodMk_left).aestronglyMeasurable
    · exact Eventually.of_forall (fun ξ => b.pathDrift_bound W s ξ)
  have hi2 := integrable_family_comp (P := W.law) F.smooth.deriv.deriv (s:ℝ) hx
  have hi3 := integrable_family_comp (P := W.law) F.rate_smooth (s:ℝ) hx
  have he : (∫ ξ, deriv (F.f s) (b.solution W.driver s ξ)*b.pathDrift W s ξ ∂W.law)+
      (1/2:ℝ)*(∫ ξ, deriv (deriv (F.f s)) (b.solution W.driver s ξ) ∂W.law)+
      (∫ ξ, F.d s (b.solution W.driver s ξ) ∂W.law) =
        ∫ ξ, F.generator b.f s (b.solution W.driver s ξ) ∂W.law := by
    have hi12 : Integrable (fun ξ => deriv (F.f s) (b.solution W.driver s ξ)*b.pathDrift W s ξ+
        (1/2:ℝ)*deriv (deriv (F.f s)) (b.solution W.driver s ξ)) W.law := hi1.add (hi2.const_mul (1/2:ℝ))
    rw [← integral_const_mul,← integral_add hi1 (hi2.const_mul (1/2:ℝ)),
      ← integral_add hi12 hi3]
    apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [generator,BoundedLipschitzDrift.pathDrift,Real.toNNReal_coe]
  rw [he] at hd
  exact hd

end TimeField
end ZeroTemperatureSK

end
end

end OAI
