import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralFixedPoint
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedVelocityIntegral
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedCollisionHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.RelativeCutoffConvergence
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionDissipation
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMildApproximation
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

section

/-! # Uniform stability of the actual regularized collision integrands -/
noncomputable section
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem pairRate_uniform_difference {N D a b c d a' b' c' d' : ℝ} (hN : 0 < N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c') (hd' : 0 ≤ d')
    (hea : |a-a'| ≤ D) (heb : |b-b'| ≤ D) (hec : |c-c'| ≤ D) (hed : |d-d'| ≤ D) :
    |pairRate N a b c d-pairRate N a' b' c' d'| ≤ 12*N*D := by
  have hp := pairRate_difference_le hN ha hb hc hd ha' hb' hc' hd'
  calc
    _ ≤ 3*N*(|a-a'|+|b-b'|+|c-c'|+|d-d'|) := hp
    _ ≤ 3*N*(D+D+D+D) := by gcongr
    _ = _ := by ring

variable {X : Type*}

theorem regularizedPreRate_difference {N D : ℝ} (hN : 0 < N)
    {f g : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (hg : ∀ p, 0 ≤ g p)
    (hfg : ∀ p, |f p-g p| ≤ D) (z : (X × (Velocity × Velocity)) × Sphere) :
    |regularizedPreRate N f z-regularizedPreRate N g z| ≤ 24*N^2*D := by
  have hw := windowKernel_bounds hN.le z
  have hp := pairRate_uniform_difference hN
    (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
    (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
    (hg (z.1.1,z.1.2.1)) (hg (z.1.1,z.1.2.2))
    (hg (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hg (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
    (hfg _) (hfg _) (hfg _) (hfg _)
  unfold regularizedPreRate
  rw [← mul_sub,abs_mul,abs_of_nonneg hw.1]
  exact (mul_le_mul hw.2 hp (abs_nonneg _) (by positivity)).trans_eq (by ring)

theorem regularizedPostRate_difference {N D : ℝ} (hN : 0 < N)
    {f g : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (hg : ∀ p, 0 ≤ g p)
    (hfg : ∀ p, |f p-g p| ≤ D) (z : (X × (Velocity × Velocity)) × Sphere) :
    |regularizedPostRate N f z-regularizedPostRate N g z| ≤ 24*N^2*D :=
  regularizedPreRate_difference hN hf hg hfg (scatterTriple z)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Global uniform stability of the positive cutoff collision operator -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def rateLipschitz (N : ℝ) : ℝ := 24*N^2*(fiberMeasure N).real Set.univ

theorem gain_difference {N D : ℝ} (hN : 0 < N)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p) (hg : ∀ p, 0 ≤ g p) (hfg : ∀ p, |f p-g p| ≤ D)
    (p : X × Velocity) : |gain N f p-gain N g p| ≤ rateLipschitz N*D := by
  unfold gain
  rw [← integral_sub (post_fiber_integrable hN hfm hf p) (post_fiber_integrable hN hgm hg p)]
  have h := norm_integral_le_of_norm_le_const (μ := fiberMeasure N)
    (ae_of_all _ (fun q => show ‖regularizedPostRate N f (collisionGrouping.symm (p,q))-
      regularizedPostRate N g (collisionGrouping.symm (p,q))‖ ≤ 24*N^2*D by
        simpa only [Real.norm_eq_abs] using regularizedPostRate_difference hN hf hg hfg _))
  rw [Real.norm_eq_abs] at h
  exact h.trans_eq (by unfold rateLipschitz; ring)

theorem loss_difference {N D : ℝ} (hN : 0 < N)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p) (hg : ∀ p, 0 ≤ g p) (hfg : ∀ p, |f p-g p| ≤ D)
    (p : X × Velocity) : |loss N f p-loss N g p| ≤ rateLipschitz N*D := by
  unfold loss
  rw [← integral_sub (pre_fiber_integrable hN hfm hf p) (pre_fiber_integrable hN hgm hg p)]
  have h := norm_integral_le_of_norm_le_const (μ := fiberMeasure N)
    (ae_of_all _ (fun q => show ‖regularizedPreRate N f (collisionGrouping.symm (p,q))-
      regularizedPreRate N g (collisionGrouping.symm (p,q))‖ ≤ 24*N^2*D by
        simpa only [Real.norm_eq_abs] using regularizedPreRate_difference hN hf hg hfg _))
  rw [Real.norm_eq_abs] at h
  exact h.trans_eq (by unfold rateLipschitz; ring)

def positiveSource (N : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  gain N f p + (lossBound N*f p-loss N f p)

theorem positiveSource_bounds {N R : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hR : ∀ p, f p ≤ R) (p : X × Velocity) :
    0 ≤ positiveSource N f p ∧ positiveSource N f p ≤ gainBound N+lossBound N*R := by
  have hgain := gain_bounds hN hfm hf p
  have hloss := loss_bounds hN hfm hf p
  have hL : 0 ≤ lossBound N := by unfold lossBound; positivity
  unfold positiveSource
  constructor
  · linarith
  · have hr := mul_le_mul_of_nonneg_left (hR p) hL
    linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The positive source used in the global cutoff iteration -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def sourceLipschitz (N : ℝ) : ℝ := 2*rateLipschitz N+lossBound N

theorem positiveSource_measurable (N : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (positiveSource N f) :=
  (gain_measurable N hf).add ((measurable_const.mul hf).sub (loss_measurable N hf))

theorem positiveSource_difference {N D : ℝ} (hN : 0 < N)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p) (hg : ∀ p, 0 ≤ g p) (hfg : ∀ p, |f p-g p| ≤ D)
    (p : X × Velocity) : |positiveSource N f p-positiveSource N g p| ≤ sourceLipschitz N*D := by
  have hgain := gain_difference hN hfm hgm hf hg hfg p
  have hloss := loss_difference hN hfm hgm hf hg hfg p
  have hL : 0 ≤ lossBound N := by unfold lossBound; positivity
  have he : positiveSource N f p-positiveSource N g p =
      (gain N f p-gain N g p)+(lossBound N*(f p-g p)-(loss N f p-loss N g p)) := by
    unfold positiveSource
    ring
  rw [he]
  calc
    _ ≤ |gain N f p-gain N g p|+|lossBound N*(f p-g p)-(loss N f p-loss N g p)| := abs_add_le _ _
    _ ≤ |gain N f p-gain N g p|+(|lossBound N*(f p-g p)|+|loss N f p-loss N g p|) := by
      gcongr
      exact abs_sub (lossBound N*(f p-g p)) (loss N f p-loss N g p)
    _ = |gain N f p-gain N g p|+(lossBound N*|f p-g p|+|loss N f p-loss N g p|) := by
      rw [abs_mul,abs_of_nonneg hL]
    _ ≤ rateLipschitz N*D+(lossBound N*D+rateLipschitz N*D) := by
      gcongr
      exact hfg p
    _ = _ := by unfold sourceLipschitz; ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Exponential rescaling of the bounded positive collision source -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

def scaledDensity (T a : ℝ) (f : ℝ × Phase → ℝ) (t : ℝ) (p : Phase) : ℝ :=
  Real.exp (a*PositiveIntegral.time T t)*f (t,p)

def scaledProfile (T a : ℝ) (f : ℝ × Phase → ℝ) (p : (ℝ × Position) × Velocity) : ℝ :=
  scaledDensity T a f p.1.1 (p.1.2,p.2)

def scaledSource (T a N : ℝ) (f : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  Real.exp (-a*PositiveIntegral.time T z.1)*positiveSource N (scaledProfile T a f)
    ((z.1,z.2.1),z.2.2)

theorem scaledSource_eq (T a N : ℝ) (f : ℝ × Phase → ℝ) (z : ℝ × Phase) :
    scaledSource T a N f z = Real.exp (-a*PositiveIntegral.time T z.1)*
      positiveSource N (scaledDensity T a f z.1) z.2 := rfl

theorem scaledDensity_measurable (T a : ℝ) {f : ℝ × Phase → ℝ} (hf : Measurable f)
    (t : ℝ) : Measurable (scaledDensity T a f t) :=
  measurable_const.mul (hf.comp (measurable_const.prodMk measurable_id))

theorem scaledProfile_measurable (T a : ℝ) {f : ℝ × Phase → ℝ} (hf : Measurable f) :
    Measurable (scaledProfile T a f) := by
  unfold scaledProfile scaledDensity PositiveIntegral.time
  fun_prop

theorem scaledSource_measurable (T a N : ℝ) {f : ℝ × Phase → ℝ} (hf : Measurable f) :
    Measurable (scaledSource T a N f) := by
  have hm := (positiveSource_measurable N (scaledProfile_measurable T a hf)).comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  apply Measurable.mul _ hm
  unfold PositiveIntegral.time
  fun_prop

theorem exp_discount_cancel (a t : ℝ) : Real.exp (-a*t)*Real.exp (a*t) = 1 := by
  rw [← Real.exp_add]
  rw [show -a*t+a*t = 0 by ring,Real.exp_zero]

theorem scaledSource_bounds {T a N R : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a) (hN : 0 < N)
    {f : ℝ × Phase → ℝ} (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hR : ∀ z, f z ≤ R) (z : ℝ × Phase) :
    0 ≤ scaledSource T a N f z ∧ scaledSource T a N f z ≤ gainBound N+lossBound N*R := by
  let s := PositiveIntegral.time T z.1
  have hs : 0 ≤ s := (PositiveIntegral.time_bounds hT z.1).1
  have hn (p : Phase) : 0 ≤ scaledDensity T a f z.1 p :=
    mul_nonneg (Real.exp_pos _).le (hf _)
  have hb (p : Phase) : scaledDensity T a f z.1 p ≤ Real.exp (a*s)*R :=
    mul_le_mul_of_nonneg_left (hR _) (Real.exp_pos _).le
  have hsrc := positiveSource_bounds hN (scaledDensity_measurable T a hfm z.1) hn hb z.2
  have hd : Real.exp (-a*s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hC : 0 ≤ gainBound N := by unfold gainBound; positivity
  rw [scaledSource_eq]
  refine ⟨mul_nonneg (Real.exp_pos _).le hsrc.1,?_⟩
  calc
    _ ≤ Real.exp (-a*s)*(gainBound N+lossBound N*(Real.exp (a*s)*R)) :=
      mul_le_mul_of_nonneg_left hsrc.2 (Real.exp_pos _).le
    _ = Real.exp (-a*s)*gainBound N+(lossBound N*R)*(Real.exp (-a*s)*Real.exp (a*s)) := by ring
    _ = Real.exp (-a*s)*gainBound N+lossBound N*R := by rw [exp_discount_cancel,mul_one]
    _ ≤ gainBound N+lossBound N*R := by
      exact add_le_add ((mul_le_mul_of_nonneg_right hd hC).trans_eq (one_mul _)) le_rfl

theorem scaledSource_difference {T a N D : ℝ} (hN : 0 < N)
    {f g : ℝ × Phase → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z) (hfg : ∀ z, |f z-g z| ≤ D)
    (z : ℝ × Phase) : |scaledSource T a N f z-scaledSource T a N g z| ≤ sourceLipschitz N*D := by
  let s := PositiveIntegral.time T z.1
  have hfn (p : Phase) : 0 ≤ scaledDensity T a f z.1 p := mul_nonneg (Real.exp_pos _).le (hf _)
  have hgn (p : Phase) : 0 ≤ scaledDensity T a g z.1 p := mul_nonneg (Real.exp_pos _).le (hg _)
  have hdiff (p : Phase) : |scaledDensity T a f z.1 p-scaledDensity T a g z.1 p| ≤
      Real.exp (a*s)*D := by
    change |Real.exp (a*s)*f (z.1,p)-Real.exp (a*s)*g (z.1,p)| ≤ _
    rw [← mul_sub,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hfg _) (Real.exp_pos _).le
  have h := positiveSource_difference hN (scaledDensity_measurable T a hfm z.1)
    (scaledDensity_measurable T a hgm z.1) hfn hgn hdiff z.2
  rw [scaledSource_eq,scaledSource_eq,← mul_sub,abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-a*s)*(sourceLipschitz N*(Real.exp (a*s)*D)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = (sourceLipschitz N*D)*(Real.exp (-a*s)*Real.exp (a*s)) := by ring
    _ = sourceLipschitz N*D := by rw [exp_discount_cancel,mul_one]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual positive cutoff solutions on every finite time interval -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

def scalingRate (N : ℝ) : ℝ := sourceLipschitz N+gainBound N+1

def dampingRate (N : ℝ) : ℝ := scalingRate N+lossBound N

theorem sourceLipschitz_nonneg (N : ℝ) : 0 ≤ sourceLipschitz N := by
  unfold sourceLipschitz rateLipschitz lossBound
  positivity

theorem scalingRate_pos {N : ℝ} (hN : 0 < N) : 0 < scalingRate N := by
  have hK := sourceLipschitz_nonneg N
  have hC : 0 ≤ gainBound N := by unfold gainBound; positivity
  unfold scalingRate
  linarith

theorem dampingRate_gt_sourceLipschitz {N : ℝ} (hN : 0 < N) :
    sourceLipschitz N < dampingRate N := by
  have hL : 0 ≤ lossBound N := by unfold lossBound; positivity
  have hC : 0 ≤ gainBound N := by unfold gainBound; positivity
  unfold dampingRate scalingRate
  linarith

theorem scaledSource_ball {N R T : ℝ} (hN : 0 < N) (hT : 0 ≤ T) (hR : 1 ≤ R)
    {f : ℝ × Phase → ℝ} (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) (hfb : ∀ z, f z ≤ R)
    (z : ℝ × Phase) : 0 ≤ scaledSource T (scalingRate N) N f z ∧
      scaledSource T (scalingRate N) N f z ≤ dampingRate N*R := by
  have hb := scaledSource_bounds hT (scalingRate_pos hN).le hN hfm hf hfb z
  have hK := sourceLipschitz_nonneg N
  have hC : 0 ≤ gainBound N := by unfold gainBound; positivity
  have ha := scalingRate_pos hN
  have har := mul_le_mul_of_nonneg_left hR ha.le
  have hCa : gainBound N ≤ scalingRate N := by unfold scalingRate; linarith
  refine ⟨hb.1,hb.2.trans ?_⟩
  unfold dampingRate
  nlinarith

theorem exists_weighted_cutoff_solution {N T A : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    {f₀ : Density} (hfm : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) :
    ∃ f : BoundedMeasurable.PositiveBall (ℝ × Phase) (max A 1), ∀ z,
      f.val z = PositiveIntegral.value T (dampingRate N) TorusFlight.flight f₀
        (scaledSource T (scalingRate N) N (fun z => f.val z)) z := by
  have hR : 1 ≤ max A 1 := le_max_right _ _
  have hL : 0 < dampingRate N :=
    (sourceLipschitz_nonneg N).trans_lt (dampingRate_gt_sourceLipschitz hN)
  apply PositiveIntegral.exists_damped_fixed_point hT hL (by linarith)
    (sourceLipschitz_nonneg N) (dampingRate_gt_sourceLipschitz hN) TorusFlight.measurable_flight hfm
    (fun p => ⟨(hf₀ p).1,(hf₀ p).2.trans (le_max_left _ _)⟩)
    (fun f => scaledSource T (scalingRate N) N (fun z => f.val z))
  · intro f
    exact scaledSource_measurable _ _ _ (BoundedMeasurable.measurable (ℝ × Phase) f.val)
  · intro f z
    exact scaledSource_ball hN hT hR (BoundedMeasurable.measurable (ℝ × Phase) f.val)
      (fun z => (f.property z).1) (fun z => (f.property z).2) z
  · intro f g z
    exact scaledSource_difference hN (BoundedMeasurable.measurable (ℝ × Phase) f.val) (BoundedMeasurable.measurable (ℝ × Phase) g.val)
      (fun z => (f.property z).1) (fun z => (g.property z).1)
      (fun z => BoundedMeasurable.dist_apply_le (ℝ × Phase) f.val g.val z) z

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Exact velocity support of the regularized collision operator -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem regularizedPreRate_zero_of_velocity {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) (hz : N < ‖z.1.2.1‖) :
    regularizedPreRate N f z = 0 := by
  have hw : z ∉ collisionWindow N := fun h => (not_lt_of_ge (collisionWindow_bounds hN h).1) hz
  simp only [regularizedPreRate,windowKernel,indicator_of_notMem hw,zero_mul]

omit [MeasurableSpace X] in
theorem regularizedPostRate_zero_of_velocity {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) (hz : N < ‖z.1.2.1‖) :
    regularizedPostRate N f z = 0 := by
  have hw : z ∉ collisionWindow N := fun h => (not_lt_of_ge (collisionWindow_bounds hN h).1) hz
  rw [regularizedPostRate_formula]
  simp only [windowKernel,indicator_of_notMem hw,zero_mul]

theorem gain_zero_of_velocity {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (p : X × Velocity) (hp : N < ‖p.2‖) : gain N f p = 0 := by
  unfold gain
  have he (q : Velocity × Sphere) : regularizedPostRate N f (collisionGrouping.symm (p,q)) = 0 :=
    regularizedPostRate_zero_of_velocity hN f _ hp
  simp only [he,integral_zero]

theorem loss_zero_of_velocity {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (p : X × Velocity) (hp : N < ‖p.2‖) : loss N f p = 0 := by
  unfold loss
  have he (q : Velocity × Sphere) : regularizedPreRate N f (collisionGrouping.symm (p,q)) = 0 :=
    regularizedPreRate_zero_of_velocity hN f _ hp
  simp only [he,integral_zero]

theorem positiveSource_outside {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (p : X × Velocity) (hp : N < ‖p.2‖) : positiveSource N f p = lossBound N*f p := by
  simp only [positiveSource,gain_zero_of_velocity hN f p hp,loss_zero_of_velocity hN f p hp,
    sub_zero,zero_add]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The common pre/post multiplier in the conservative approximation -/
noncomputable section
open Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

def attenuation (N S : ℝ) : ℝ := N^2/(N+S)^2

theorem attenuation_nonneg (N S : ℝ) : 0 ≤ attenuation N S :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem attenuation_le_one {N S : ℝ} (hN : 0 < N) (hS : 0 ≤ S) : attenuation N S ≤ 1 := by
  have hp : 0 < N+S := add_pos_of_pos_of_nonneg hN hS
  apply (div_le_one (sq_pos_of_pos hp)).mpr
  exact (sq_le_sq₀ hN.le hp.le).mpr (by linarith)

theorem attenuation_tendsto (S : ℝ) : Tendsto (fun N : ℝ => attenuation N S) atTop (𝓝 1) := by
  have h := pairRate_tendsto 1 1 (S-2) 0
  have he (N : ℝ) : pairRate N 1 1 (S-2) 0 = attenuation N S := by
    rw [pairRate_eq]
    unfold attenuation rateSum
    congr 1 <;> ring
  simpa only [he,one_mul] using h

def rateMultiplier {X : Type*} (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  attenuation N (rateSum (f (z.1.1,z.1.2.1)) (f (z.1.1,z.1.2.2))
    (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)))

variable {X : Type*}

theorem rateMultiplier_bounds {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ rateMultiplier N f z ∧ rateMultiplier N f z ≤ 1 := by
  exact ⟨attenuation_nonneg _ _,attenuation_le_one hN
    (rateSum_nonneg (hf _) (hf _) (hf _) (hf _))⟩

theorem regularizedPreRate_factor (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    regularizedPreRate N f z = windowKernel N z*rateMultiplier N f z*
      f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2) := by
  unfold regularizedPreRate
  rw [pairRate_eq]
  unfold rateMultiplier attenuation
  ring

theorem regularizedPostRate_factor (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    regularizedPostRate N f z = windowKernel N z*rateMultiplier N f z*
      f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*
      f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) := by
  rw [regularizedPostRate_formula,pairRate_eq]
  unfold rateMultiplier attenuation rateSum
  ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integrability of the bounded collision rates without a quadratic moment assumption -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def pairBall (N : ℝ) : Set (Velocity × Velocity) :=
  Metric.closedBall 0 N ×ˢ Metric.closedBall 0 N

theorem pairBall_compact (N : ℝ) : IsCompact (pairBall N) :=
  (isCompact_closedBall (0 : Velocity) N).prod (isCompact_closedBall (0 : Velocity) N)

omit [MeasurableSpace X] in
theorem regularizedPreRate_zero_of_outside {N : ℝ} (hN : 0 ≤ N)
    (f : X × Velocity → ℝ) {z : (X × (Velocity × Velocity)) × Sphere}
    (hz : z.1.2 ∉ pairBall N) : regularizedPreRate N f z = 0 := by
  have hw : z ∉ collisionWindow N := by
    intro h
    have hb := collisionWindow_bounds hN h
    apply hz
    simpa only [pairBall,Set.mem_prod,Metric.mem_closedBall,dist_zero_right] using hb
  simp only [regularizedPreRate,windowKernel,indicator_of_notMem hw,zero_mul]

theorem regularizedPreRate_integrable {N : ℝ} (hN : 0 < N) {μ : Measure X} [IsFiniteMeasure μ]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    Integrable (regularizedPreRate N f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hi : Integrable ((pairBall N).indicator (fun _ : Velocity × Velocity => 2*N^3))
      (volume : Measure (Velocity × Velocity)) :=
    (integrableOn_const (pairBall_compact N).measure_lt_top.ne).integrable_indicator
      (pairBall_compact N).measurableSet
  have hh := (hi.comp_snd μ).comp_fst sphereArea
  apply hh.mono' (regularizedPreRate_measurable N hfm).aestronglyMeasurable
  filter_upwards [] with z
  change ‖regularizedPreRate N f z‖ ≤ (pairBall N).indicator (fun _ => 2*N^3) z.1.2
  by_cases hz : z.1.2 ∈ pairBall N
  · rw [indicator_of_mem hz,Real.norm_of_nonneg (regularizedPreRate_bounds hN hf z).1]
    exact (regularizedPreRate_bounds hN hf z).2
  · rw [regularizedPreRate_zero_of_outside hN.le f hz,indicator_of_notMem hz,norm_zero]

theorem regularizedPostRate_integrable {N : ℝ} (hN : 0 < N) {μ : Measure X} [IsFiniteMeasure μ]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    Integrable (regularizedPostRate N f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) :=
  (scatterTriple_measurePreserving μ).integrable_comp_of_integrable
    (regularizedPreRate_integrable hN hfm hf)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Compact velocity tests of the approximate collision rates are integrable -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem regularizedPreRate_test_integrable {N C : ℝ} (hN : 0 < N)
    {μ : Measure X} [IsFiniteMeasure μ] {f ψ : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hψm : Measurable ψ)
    (hψ : ∀ p, ‖p.2‖ ≤ N → |ψ p| ≤ C) :
    Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPreRate N f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hi := (regularizedPreRate_integrable (μ := μ) hN hfm hf).norm.const_mul C
  apply hi.mono'
    ((hψm.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)).mul
      (regularizedPreRate_measurable N hfm)).aestronglyMeasurable
  filter_upwards [] with z
  change ‖ψ (z.1.1,z.1.2.1)*regularizedPreRate N f z‖ ≤ C*‖regularizedPreRate N f z‖
  by_cases hz : N < ‖z.1.2.1‖
  · rw [regularizedPreRate_zero_of_velocity hN.le f z hz,mul_zero,norm_zero,mul_zero]
  · rw [norm_mul,Real.norm_eq_abs (ψ _)]
    exact mul_le_mul_of_nonneg_right (hψ _ (le_of_not_gt hz)) (norm_nonneg _)

theorem regularizedPostRate_test_integrable {N C : ℝ} (hN : 0 < N)
    {μ : Measure X} [IsFiniteMeasure μ] {f ψ : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hψm : Measurable ψ)
    (hψ : ∀ p, ‖p.2‖ ≤ N → |ψ p| ≤ C) :
    Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPostRate N f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hi := (regularizedPostRate_integrable (μ := μ) hN hfm hf).norm.const_mul C
  apply hi.mono'
    ((hψm.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)).mul
      (regularizedPostRate_measurable N hfm)).aestronglyMeasurable
  filter_upwards [] with z
  change ‖ψ (z.1.1,z.1.2.1)*regularizedPostRate N f z‖ ≤ C*‖regularizedPostRate N f z‖
  by_cases hz : N < ‖z.1.2.1‖
  · rw [regularizedPostRate_zero_of_velocity hN.le f z hz,mul_zero,norm_zero,mul_zero]
  · rw [norm_mul,Real.norm_eq_abs (ψ _)]
    exact mul_le_mul_of_nonneg_right (hψ _ (le_of_not_gt hz)) (norm_nonneg _)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The finite partner integral equals the full physical collision integral -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem regularizedPreRate_zero_of_partner {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) (hz : N < ‖z.1.2.2‖) :
    regularizedPreRate N f z = 0 := by
  rw [← regularizedPreRate_particleSwap N f z]
  exact regularizedPreRate_zero_of_velocity hN f _ hz

theorem regularizedPostRate_zero_of_partner {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) (hz : N < ‖z.1.2.2‖) :
    regularizedPostRate N f z = 0 := by
  rw [← regularizedPostRate_particleSwap N f z]
  exact regularizedPostRate_zero_of_velocity hN f _ hz

theorem fiberMeasure_eq_restrict (N : ℝ) : fiberMeasure N =
    ((volume : Measure Velocity).prod sphereArea).restrict (Metric.closedBall 0 N ×ˢ Set.univ) := by
  simpa only [fiberMeasure,Measure.restrict_univ] using
    (Measure.prod_restrict (μ := (volume : Measure Velocity)) (ν := sphereArea)
      (Metric.closedBall 0 N) Set.univ)

theorem loss_eq_full_integral {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ) (p : X × Velocity) :
    loss N f p = ∫ q, regularizedPreRate N f (collisionGrouping.symm (p,q))
      ∂((volume : Measure Velocity).prod sphereArea) := by
  rw [loss,fiberMeasure_eq_restrict,← integral_indicator (measurableSet_closedBall.prod MeasurableSet.univ)]
  apply integral_congr_ae
  filter_upwards [] with q
  by_cases hq : q ∈ Metric.closedBall 0 N ×ˢ (Set.univ : Set Sphere)
  · exact indicator_of_mem hq _
  · rw [indicator_of_notMem hq]
    symm
    apply regularizedPreRate_zero_of_partner hN
    change N < ‖q.1‖
    simpa only [Set.mem_prod,Set.mem_univ,and_true,Metric.mem_closedBall,dist_zero_right,not_le] using hq

theorem gain_eq_full_integral {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ) (p : X × Velocity) :
    gain N f p = ∫ q, regularizedPostRate N f (collisionGrouping.symm (p,q))
      ∂((volume : Measure Velocity).prod sphereArea) := by
  rw [gain,fiberMeasure_eq_restrict,← integral_indicator (measurableSet_closedBall.prod MeasurableSet.univ)]
  apply integral_congr_ae
  filter_upwards [] with q
  by_cases hq : q ∈ Metric.closedBall 0 N ×ˢ (Set.univ : Set Sphere)
  · exact indicator_of_mem hq _
  · rw [indicator_of_notMem hq]
    symm
    apply regularizedPostRate_zero_of_partner hN
    change N < ‖q.1‖
    simpa only [Set.mem_prod,Set.mem_univ,and_true,Metric.mem_closedBall,dist_zero_right,not_le] using hq

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The conservative weak identity for the bounded-rate approximation -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem integral_regularizedPostRate_scatter_right (μ : Measure X) [SFinite μ] (N : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.2)*regularizedPostRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*regularizedPreRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.2)*regularizedPostRate N f z)
  simp only [regularizedPostRate_scatter] at h
  exact h.symm

theorem regularized_weak_identity {μ : Measure X} [SFinite μ] (b : ℝ) (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) -
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    (1/2:ℝ) * ∫ z, collisionJump ψ z*regularizedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  have hr : Integrable (fun z => ψ (z.1.1,z.1.2.2)*regularizedPreRate b f z) ν := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpre
    simp only [Function.comp_def,regularizedPreRate_particleSwap] at h
    exact h
  have hrpost : Integrable (fun z => ψ (z.1.1,z.1.2.2)*regularizedPostRate b f z) ν := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,regularizedPostRate_particleSwap] at h
    exact h
  have hl' : Integrable (fun z =>
      ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*regularizedPreRate b f z) ν := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,regularizedPostRate_scatter] at h
    exact h
  have hr' : Integrable (fun z =>
      ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*regularizedPreRate b f z) ν := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hrpost
    simp only [Function.comp_def,regularizedPostRate_scatter] at h
    exact h
  have he : (fun z => collisionJump ψ z*regularizedPreRate b f z) =
      (fun z => ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*regularizedPreRate b f z)+
      (fun z => ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*regularizedPreRate b f z)-
      (fun z => ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z)-
      (fun z => ψ (z.1.1,z.1.2.2)*regularizedPreRate b f z) := by
    funext z
    dsimp [collisionJump]
    ring
  rw [he,integral_sub' ((hl'.add hr').sub hpre) hr,
    integral_sub' (hl'.add hr') hpre,integral_add' hl' hr']
  rw [← integral_regularizedPostRate_scatter,← integral_regularizedPostRate_scatter_right,
    ← integral_regularizedPostRate_swap,← integral_regularizedPreRate_swap]
  ring

theorem regularized_collision_invariant {μ : Measure X} [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hψ : ∀ z, collisionJump ψ z = 0) :
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := regularized_weak_identity b f ψ hpre hpost
  simp only [hψ,zero_mul,integral_zero,mul_zero,sub_eq_zero] at h
  exact h


end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Mass, momentum, and energy for the actual bounded-rate collision operator -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem regularized_test_marginals {N C : ℝ} (hN : 0 < N)
    {μ : Measure X} [IsFiniteMeasure μ] {f ψ : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hψm : Measurable ψ)
    (hψ : ∀ p, ‖p.2‖ ≤ N → |ψ p| ≤ C) :
    Integrable (fun p => ψ p*gain N f p) (μ.prod volume) ∧
    Integrable (fun p => ψ p*loss N f p) (μ.prod volume) ∧
    (∫ p, ψ p*gain N f p ∂μ.prod volume) =
      ∫ z, ψ (z.1.1,z.1.2.1)*regularizedPostRate N f z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea ∧
    (∫ p, ψ p*loss N f p ∂μ.prod volume) =
      ∫ z, ψ (z.1.1,z.1.2.1)*regularizedPreRate N f z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have hp := collision_test_marginal (regularizedPostRate N f) ψ
    (regularizedPostRate_test_integrable (μ := μ) hN hfm hf hψm hψ)
  have hl := collision_test_marginal (regularizedPreRate N f) ψ
    (regularizedPreRate_test_integrable (μ := μ) hN hfm hf hψm hψ)
  simp only [← gain_eq_full_integral hN.le f] at hp
  simp only [← loss_eq_full_integral hN.le f] at hl
  exact ⟨hp.1,hl.1,hp.2,hl.2⟩

theorem regularized_test_invariant {N C : ℝ} (hN : 0 < N)
    {μ : Measure X} [IsFiniteMeasure μ] {f ψ : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hψm : Measurable ψ)
    (hψ : ∀ p, ‖p.2‖ ≤ N → |ψ p| ≤ C) (hj : ∀ z, collisionJump ψ z = 0) :
    (∫ p, ψ p*gain N f p ∂μ.prod volume) = ∫ p, ψ p*loss N f p ∂μ.prod volume := by
  obtain ⟨_,_,hp,hl⟩ := regularized_test_marginals (μ := μ) hN hfm hf hψm hψ
  rw [hp,hl]
  exact regularized_collision_invariant N f ψ
    (regularizedPreRate_test_integrable hN hfm hf hψm hψ)
    (regularizedPostRate_test_integrable hN hfm hf hψm hψ) hj

theorem regularized_mass_balance {N : ℝ} (hN : 0 < N)
    {μ : Measure X} [IsFiniteMeasure μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    (∫ p, gain N f p ∂μ.prod volume) = ∫ p, loss N f p ∂μ.prod volume := by
  simpa only [one_mul] using regularized_test_invariant (μ := μ) (C := 1) hN hfm hf
    (ψ := fun _ => (1:ℝ)) measurable_const (fun _ _ => by norm_num)
    (collisionJump_mass (fun _ => 1))

theorem regularized_energy_balance {N : ℝ} (hN : 0 < N)
    {μ : Measure X} [IsFiniteMeasure μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    (∫ p, ‖p.2‖^2*gain N f p ∂μ.prod volume) = ∫ p, ‖p.2‖^2*loss N f p ∂μ.prod volume := by
  apply regularized_test_invariant (μ := μ) (C := N^2) hN hfm hf
    (ψ := fun p => ‖p.2‖^2) (measurable_snd.norm.pow_const 2) _ collisionJump_energy
  intro p hp
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hN.le).mpr hp

theorem regularized_momentum_balance {N : ℝ} (hN : 0 < N)
    {μ : Measure X} [IsFiniteMeasure μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (i : Fin 3) :
    (∫ p : X × Velocity, (p.2 i)*gain N f p ∂μ.prod volume) = ∫ p : X × Velocity, (p.2 i)*loss N f p ∂μ.prod volume := by
  apply regularized_test_invariant (μ := μ) (C := N) hN hfm hf
    (ψ := fun p => p.2 i) (by fun_prop) _ (collisionJump_momentum i)
  intro p hp
  have h : |p.2 i| ≤ ‖p.2‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p.2 i
  exact h.trans hp

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Symmetric collision production and its entropy sign -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem integral_jump_post (μ : Measure X) [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, collisionJump ψ z*regularizedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    -(∫ z, collisionJump ψ z*regularizedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => collisionJump ψ z*regularizedPostRate b f z)
  simp only [collisionJump_scatter,regularizedPostRate_scatter,neg_mul,integral_neg] at h
  exact h.symm

theorem collisionJump_integrable {μ : Measure X} [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (fun z => collisionJump ψ z*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ∧
    Integrable (fun z => collisionJump ψ z*regularizedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hr : Integrable (fun z => ψ (z.1.1,z.1.2.2)*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpre
    simp only [Function.comp_def,regularizedPreRate_particleSwap] at h
    exact h
  have hrpost : Integrable (fun z => ψ (z.1.1,z.1.2.2)*regularizedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,regularizedPostRate_particleSwap] at h
    exact h
  have hl' : Integrable (fun z =>
      ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,regularizedPostRate_scatter] at h
    exact h
  have hr' : Integrable (fun z =>
      ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hrpost
    simp only [Function.comp_def,regularizedPostRate_scatter] at h
    exact h
  have hp : Integrable (fun z => collisionJump ψ z*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := ((hl'.add hr').sub hpre).sub hr
    convert h using 1
    funext z
    dsimp [collisionJump]
    ring
  refine ⟨hp,?_⟩
  have ht := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hp
  simp only [Function.comp_def,collisionJump_scatter,neg_mul] at ht
  convert ht.neg using 1
  funext z
  simp only [Pi.neg_apply,neg_neg]
  rfl

theorem regularized_production_identity {μ : Measure X} [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    :
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) -
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    -(1/4:ℝ) * ∫ z, collisionJump ψ z*(regularizedPostRate b f z-regularizedPreRate b f z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  obtain ⟨hjpre,hjpost⟩ := collisionJump_integrable b f ψ hpre hpost
  simp_rw [mul_sub]
  rw [integral_sub hjpost hjpre,integral_jump_post]
  have h := regularized_weak_identity b f ψ hpre hpost
  linarith


end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Entropy sign for the symmetric bounded-rate collision operator -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem regularized_entropy_production_nonneg (b : ℝ) (f : X × Velocity → ℝ) (hf : ∀ p, 0 < f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ collisionJump (fun p => Real.log (f p)) z*
      (regularizedPostRate b f z-regularizedPreRate b f z) := by
  let A := f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)
  let B := f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)
  have hA : 0 < A := mul_pos (hf _) (hf _)
  have hB : 0 < B := mul_pos (hf _) (hf _)
  have hsign : 0 ≤ (Real.log A-Real.log B)*(A-B) := by
    by_cases hBA : B ≤ A
    · exact mul_nonneg (sub_nonneg.mpr (Real.log_le_log hB hBA)) (sub_nonneg.mpr hBA)
    · have hAB : A ≤ B := le_of_lt (lt_of_not_ge hBA)
      exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (Real.log_le_log hA hAB)) (sub_nonpos.mpr hAB)
  rw [collisionJump_log_density f hf,Real.log_div hA.ne' hB.ne']
  rw [regularizedPostRate_factor,regularizedPreRate_factor]
  have he : windowKernel b z*rateMultiplier b f z*
      f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*
      f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)-
      windowKernel b z*rateMultiplier b f z*f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2) =
      (windowKernel b z*rateMultiplier b f z)*(A-B) := by dsimp [A,B]; ring
  rw [he]
  have hw : 0 ≤ windowKernel b z := by
    by_cases hz : z ∈ collisionWindow b
    · rw [windowKernel,Set.indicator_of_mem hz]
      exact collisionKernel_nonneg _ _ _
    · rw [windowKernel,Set.indicator_of_notMem hz]
  have hk := mul_nonneg hw (attenuation_nonneg b
    (rateSum (f (z.1.1,z.1.2.1)) (f (z.1.1,z.1.2.2))
      (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
      (f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))))
  change 0 ≤ windowKernel b z*rateMultiplier b f z at hk
  convert mul_nonneg hk hsign using 1
  ring

omit [MeasurableSpace X] in
theorem regularized_relative_production_nonneg (N : ℝ) (f : X × Velocity → ℝ)
    (hf : ∀ p, 0 < f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ collisionJump (fun p => Real.log (f p/maxwellian p.2)) z*
      (regularizedPostRate N f z-regularizedPreRate N f z) := by
  rw [collisionJump_log_relative f hf]
  exact regularized_entropy_production_nonneg N f hf z

theorem regularized_relative_entropy_nonpositive {μ : Measure X} [IsFiniteMeasure μ]
    {N C : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hf : ∀ p, 0 < f p)
    (hlog : ∀ p, ‖p.2‖ ≤ N → |Real.log (f p/maxwellian p.2)| ≤ C) :
    (∫ p, Real.log (f p/maxwellian p.2)*gain N f p ∂μ.prod volume)-
      (∫ p, Real.log (f p/maxwellian p.2)*loss N f p ∂μ.prod volume) ≤ 0 := by
  have hψ : Measurable (fun p => Real.log (f p/maxwellian p.2)) := by
    have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by
      unfold maxwellian; fun_prop
    exact (hfm.div hm).log
  have hpre := regularizedPreRate_test_integrable (μ := μ) hN hfm
    (fun p => (hf p).le) hψ hlog
  have hpost := regularizedPostRate_test_integrable (μ := μ) hN hfm
    (fun p => (hf p).le) hψ hlog
  obtain ⟨_,_,hp,hl⟩ := regularized_test_marginals (μ := μ) hN hfm (fun p => (hf p).le) hψ hlog
  rw [hp,hl,regularized_production_identity N f (fun p => Real.log (f p/maxwellian p.2)) hpre hpost]
  have hn : 0 ≤ ∫ z, collisionJump (fun p => Real.log (f p/maxwellian p.2)) z*
      (regularizedPostRate N f z-regularizedPreRate N f z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea :=
    MeasureTheory.integral_nonneg (regularized_relative_production_nonneg N f hf)
  linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The bounded collision operator is stable under positive Gaussian shifts -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def gaussianShift (δ : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  f p+δ*maxwellian p.2

theorem gaussianShift_measurable (δ : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (gaussianShift δ f) := by
  have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  exact hf.add (hm.const_mul δ)

omit [MeasurableSpace X] in
theorem gaussianShift_pos {δ : ℝ} (hδ : 0 < δ) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) : 0 < gaussianShift δ f p :=
  add_pos_of_nonneg_of_pos (hf p) (mul_pos hδ (maxwellian_pos p.2))

omit [MeasurableSpace X] in
theorem gaussianShift_difference {δ : ℝ} (hδ : 0 ≤ δ) (f : X × Velocity → ℝ)
    (p : X × Velocity) : |f p-gaussianShift δ f p| ≤ δ*maxwellian 0 := by
  rw [gaussianShift,show f p-(f p+δ*maxwellian p.2) = -(δ*maxwellian p.2) by ring,
    abs_neg,abs_of_nonneg (mul_nonneg hδ (maxwellian_pos _).le)]
  exact mul_le_mul_of_nonneg_left (maxwellian_le_center p.2) hδ

def collisionOperator (N : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  gain N f p-loss N f p

theorem collisionOperator_measurable (N : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (collisionOperator N f) :=
  (gain_measurable N hf).sub (loss_measurable N hf)

theorem collisionOperator_support {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (p : X × Velocity) (hp : N < ‖p.2‖) : collisionOperator N f p = 0 := by
  rw [collisionOperator,gain_zero_of_velocity hN f p hp,loss_zero_of_velocity hN f p hp,sub_self]

theorem collisionOperator_gaussian_difference {N δ : ℝ} (hN : 0 < N) (hδ : 0 < δ)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (p : X × Velocity) :
    |collisionOperator N f p-collisionOperator N (gaussianShift δ f) p| ≤
      2*rateLipschitz N*δ*maxwellian 0 := by
  have hg := gaussianShift_measurable δ hfm
  have hgn := fun p => (gaussianShift_pos hδ hf p).le
  have ha := gain_difference hN hfm hg hf hgn (gaussianShift_difference hδ.le f) p
  have hb := loss_difference hN hfm hg hf hgn (gaussianShift_difference hδ.le f) p
  calc
    _ = |(gain N f p-gain N (gaussianShift δ f) p)-
          (loss N f p-loss N (gaussianShift δ f) p)| := by unfold collisionOperator; congr 1; ring
    _ ≤ |gain N f p-gain N (gaussianShift δ f) p|+
          |loss N f p-loss N (gaussianShift δ f) p| := abs_sub _ _
    _ ≤ _ := by linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integrable endpoint entropy and removal of positive regularization -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem regularizedEntropy_parameter_continuous :
    Continuous (fun p : (ℝ × ℝ) × Velocity =>
      regularizedEntropy (maxwellian p.2) (maxwellian p.2) p.1.1 p.1.2) := by
  have hm : Continuous maxwellian := by unfold maxwellian; fun_prop
  have hl : Continuous (fun p : (ℝ × ℝ) × Velocity => Real.log (maxwellian p.2)) :=
    (hm.comp continuous_snd).log (fun p => (maxwellian_pos p.2).ne')
  unfold regularizedEntropy scalarRelativeEntropy
  fun_prop

theorem regularizedEntropy_uniform_bound (N B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ ∈ Icc (0:ℝ) 1, ∀ a ∈ Icc (0:ℝ) B, ∀ v : Velocity,
      ‖v‖ ≤ N → |regularizedEntropy (maxwellian v) (maxwellian v) δ a| ≤ C := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc.prod isCompact_Icc).prod (isCompact_closedBall (0:Velocity) N)).exists_bound_of_continuousOn
    regularizedEntropy_parameter_continuous.continuousOn
  refine ⟨|C|,abs_nonneg _,?_⟩
  intro δ hδ a ha v hv
  have h := hC ((δ,a),v) ⟨⟨hδ,ha⟩,by simpa only [Metric.mem_closedBall,dist_zero_right] using hv⟩
  have hb : |regularizedEntropy (maxwellian v) (maxwellian v) δ a| ≤ C := by
    simpa only [Real.norm_eq_abs] using h
  exact hb.trans (le_abs_self C)

variable {X : Type*} [MeasurableSpace X]

theorem scalarRelativeEntropy_measurable {m a : X → ℝ} (hm : Measurable m) (ha : Measurable a) :
    Measurable (fun p => scalarRelativeEntropy (m p) (a p)) :=
  ((Real.continuous_mul_log.measurable.comp ha).sub
    (ha.mul (measurable_const.add hm.log))).add hm

theorem regularizedEntropy_measurable (δ : ℝ) {f : X × Velocity → ℝ} (hfm : Measurable f) :
    Measurable (fun p => regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f p)) := by
  have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  exact ((scalarRelativeEntropy_measurable hm (hfm.add (hm.const_mul δ))).sub
    (scalarRelativeEntropy_measurable hm (hm.const_mul δ))).add hm

theorem regularizedEntropy_integrable {μ : Measure X} [IsFiniteMeasure μ]
    {N B δ : ℝ} (hδ : δ ∈ Icc (0:ℝ) 1) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ B)
    (hfs : ∀ p, N < ‖p.2‖ → f p = 0) :
    Integrable (fun p => regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f p))
      (μ.prod volume) := by
  obtain ⟨C,hC,hCb⟩ := regularizedEntropy_uniform_bound N B
  have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  have he : Integrable (fun p => regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f p)-maxwellian p.2)
      (μ.prod volume) := by
    apply bounded_velocity_integrable (N := N) ((regularizedEntropy_measurable δ hfm).sub hm)
      (A := C+maxwellian 0)
    · intro p
      change |regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f p)-maxwellian p.2| ≤ C+maxwellian 0
      by_cases hp : N < ‖p.2‖
      · simp only [hfs p hp,regularizedEntropy,zero_add,sub_self,abs_zero]
        exact add_nonneg hC (maxwellian_pos 0).le
      · exact (abs_sub _ _).trans (add_le_add (hCb δ hδ (f p) ⟨hf p,hfb p⟩ p.2 (le_of_not_gt hp))
          ((abs_of_pos (maxwellian_pos _)).trans_le (maxwellian_le_center _)))
    · intro p hp
      simp [hfs p hp,regularizedEntropy]
  convert he.add (integrable_maxwellian.comp_snd μ) using 1
  funext p
  simp only [Pi.add_apply,sub_add_cancel]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Vanishing Gaussian error in the actual approximate entropy production -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem entropy_error_bound {N B δ : ℝ} (hN : 0 < N) (hB : 0 ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ B) (p : X × Velocity) :
    |Real.log (gaussianShift δ f p/maxwellian p.2)*
      (collisionOperator N f p-collisionOperator N (gaussianShift δ f) p)| ≤
      (|Real.log δ|+logRegularizationConstant N B)*(2*rateLipschitz N*δ*maxwellian 0) := by
  have hL : 0 ≤ rateLipschitz N := by unfold rateLipschitz; positivity
  have hC : 0 ≤ logRegularizationConstant N B := abs_nonneg _
  by_cases hp : N < ‖p.2‖
  · rw [collisionOperator_support hN.le f p hp,
      collisionOperator_support hN.le (gaussianShift δ f) p hp,sub_self,mul_zero,abs_zero]
    exact mul_nonneg (add_nonneg (abs_nonneg _) hC)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hδ.le) (maxwellian_pos 0).le)
  · rw [abs_mul]
    exact mul_le_mul (log_regularization_bound hN.le hB hδ hδ1 (hf p) (hfb p) p.2
      (le_of_not_gt hp)) (collisionOperator_gaussian_difference hN hδ hfm hf p)
      (abs_nonneg _) (add_nonneg (abs_nonneg _) hC)

def entropyErrorCoefficient (μ : Measure X) (N : ℝ) : ℝ :=
  μ.real univ*(volume : Measure Velocity).real (Metric.closedBall 0 N)*
    (2*rateLipschitz N*maxwellian 0)

theorem entropy_error_integral {μ : Measure X} [IsFiniteMeasure μ]
    {N B δ : ℝ} (hN : 0 < N) (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ B) :
    |∫ p, Real.log (gaussianShift δ f p/maxwellian p.2)*
      (collisionOperator N f p-collisionOperator N (gaussianShift δ f) p) ∂μ.prod volume| ≤
      entropyErrorCoefficient μ N*δ*(|Real.log δ|+logRegularizationConstant N B) := by
  have he := bounded_velocity_integral_bound (μ := μ) (N := N)
    (entropy_error_bound hN hB hδ hδ1 hfm hf hfb)
    (fun p hp => by rw [collisionOperator_support hN.le f p hp,
      collisionOperator_support hN.le (gaussianShift δ f) p hp,sub_self,mul_zero])
  exact he.trans_eq (by unfold entropyErrorCoefficient; ring)

theorem entropy_error_tendsto (μ : Measure X) (N B : ℝ) :
    Tendsto (fun δ : ℝ => entropyErrorCoefficient μ N*δ*
      (|Real.log δ|+logRegularizationConstant N B)) (𝓝 0) (𝓝 0) := by
  have h := (tendsto_mul_affine_abs_log_zero (logRegularizationConstant N B) 1).const_mul
    (entropyErrorCoefficient μ N)
  convert h using 1
  · funext δ; ring
  · ring_nf

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Localization of the positive iteration to its preserved velocity ball -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def velocityRegion (N : ℝ) : Set (ℝ × Phase) := {z | ‖z.2.2‖ ≤ N}

def localize (N : ℝ) (f : ℝ × Phase → ℝ) : ℝ × Phase → ℝ := (velocityRegion N).indicator f

theorem velocityRegion_measurable (N : ℝ) : MeasurableSet (velocityRegion N) :=
  measurableSet_le (by fun_prop) measurable_const

theorem localize_measurable (N : ℝ) {f : ℝ × Phase → ℝ} (hf : Measurable f) :
    Measurable (localize N f) := hf.indicator (velocityRegion_measurable N)

theorem localize_bounds {N C : ℝ} (hC : 0 ≤ C) {f : ℝ × Phase → ℝ}
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ C) (z : ℝ × Phase) :
    0 ≤ localize N f z ∧ localize N f z ≤ C := by
  by_cases hz : z ∈ velocityRegion N
  · simpa only [localize,indicator_of_mem hz] using hf z
  · simpa only [localize,indicator_of_notMem hz] using And.intro le_rfl hC

theorem localize_difference {N D : ℝ} (hD : 0 ≤ D) {f g : ℝ × Phase → ℝ}
    (hfg : ∀ z, |f z-g z| ≤ D) (z : ℝ × Phase) : |localize N f z-localize N g z| ≤ D := by
  by_cases hz : z ∈ velocityRegion N
  · simpa only [localize,indicator_of_mem hz] using hfg z
  · simpa only [localize,indicator_of_notMem hz,sub_self,abs_zero] using hD

theorem localized_fixed_point_zero {N T L : ℝ} (f₀ : Density)
    (h₀ : ∀ p, N < ‖p.2‖ → f₀ p = 0) {f g : ℝ × Phase → ℝ}
    (hf : ∀ z, f z = PositiveIntegral.value T L TorusFlight.flight f₀ (localize N g) z)
    (z : ℝ × Phase) (hz : N < ‖z.2.2‖) : f z = 0 := by
  rw [hf]
  unfold PositiveIntegral.value
  have hinit : f₀ (TorusFlight.flight (-PositiveIntegral.time T z.1) z.2) = 0 := h₀ _ hz
  rw [hinit,mul_zero,zero_add]
  have he (r : ℝ) : localize N g (r,TorusFlight.flight (r-PositiveIntegral.time T z.1) z.2) = 0 := by
    apply indicator_of_notMem
    exact not_le_of_gt hz
  simp only [he,mul_zero,intervalIntegral.integral_zero]

theorem localized_scaledSource_eq {N T a : ℝ} (hN : 0 ≤ N) {f : ℝ × Phase → ℝ}
    (hf : ∀ z, N < ‖z.2.2‖ → f z = 0) :
    localize N (scaledSource T a N f) = scaledSource T a N f := by
  funext z
  by_cases hz : z ∈ velocityRegion N
  · exact indicator_of_mem hz _
  · have ho : N < ‖z.2.2‖ := lt_of_not_ge hz
    rw [localize,indicator_of_notMem hz,scaledSource_eq,positiveSource_outside hN _ z.2 ho]
    simp only [scaledDensity,hf z ho,mul_zero]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Removing entropy regularization from supported bounded densities -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def entropyCompactMajorant (N C : ℝ) (v : Velocity) : ℝ :=
  (Metric.closedBall (0:Velocity) N).indicator (fun _ => C) v+maxwellian v

theorem entropyCompactMajorant_integrable (N C : ℝ) : Integrable (entropyCompactMajorant N C) := by
  exact ((integrableOn_const (isCompact_closedBall (0:Velocity) N).measure_lt_top.ne).integrable_indicator
    Metric.isClosed_closedBall.measurableSet).add integrable_maxwellian

omit [MeasurableSpace X] in
theorem regularizedEntropy_majorant {N B C : ℝ}
    (hCb : ∀ δ ∈ Icc (0:ℝ) 1, ∀ a ∈ Icc (0:ℝ) B, ∀ v : Velocity,
      ‖v‖ ≤ N → |regularizedEntropy (maxwellian v) (maxwellian v) δ a| ≤ C)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ B)
    (hfs : ∀ p, N < ‖p.2‖ → f p = 0) {δ : ℝ} (hδ : δ ∈ Icc (0:ℝ) 1) (p : X × Velocity) :
    ‖regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f p)‖ ≤
      entropyCompactMajorant N C p.2 := by
  rw [Real.norm_eq_abs]
  by_cases hp : p.2 ∈ Metric.closedBall 0 N
  · have hv : ‖p.2‖ ≤ N := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp
    exact (hCb δ hδ (f p) ⟨hf p,hfb p⟩ p.2 hv).trans (by
      unfold entropyCompactMajorant
      rw [indicator_of_mem hp]
      linarith [maxwellian_pos p.2])
  · have hv : N < ‖p.2‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hp
    simp only [hfs p hv,regularizedEntropy,zero_add,sub_self,abs_of_pos (maxwellian_pos p.2),
      entropyCompactMajorant,indicator_of_notMem hp]
    exact le_rfl

theorem regularizedEntropy_integral_tendsto {μ : Measure X} [IsFiniteMeasure μ]
    {N B : ℝ} {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hfb : ∀ p, f p ≤ B) (hfs : ∀ p, N < ‖p.2‖ → f p = 0) :
    Tendsto (fun δ : ℝ => ∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f p) ∂μ.prod volume)
      (𝓝[>] 0) (𝓝 (∫ p, scalarRelativeEntropy (maxwellian p.2) (f p) ∂μ.prod volume)) := by
  obtain ⟨C,_,hCb⟩ := regularizedEntropy_uniform_bound N B
  apply tendsto_integral_filter_of_dominated_convergence (fun p => entropyCompactMajorant N C p.2)
  · exact Eventually.of_forall (fun δ => (regularizedEntropy_measurable δ hfm).aestronglyMeasurable)
  · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hδ
    exact Eventually.of_forall (regularizedEntropy_majorant hCb hf hfb hfs ⟨hδ.1.le,hδ.2.le⟩)
  · exact (entropyCompactMajorant_integrable N C).comp_snd μ
  · exact Eventually.of_forall (fun p =>
      (regularizedEntropy_tendsto (maxwellian p.2) (maxwellian p.2) (f p)).mono_left nhdsWithin_le_nhds)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Positive mild cutoff solutions without the auxiliary exponential weight -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem exists_finite_cutoff_mild {N T A : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    {f₀ : Density} (hfm : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) :
    ∃ F : ℝ × Phase → ℝ, Measurable F ∧
      (∀ z, 0 ≤ F z ∧ F z ≤ Real.exp (scalingRate N*T)*max A 1) ∧
      ∀ z, F z = PositiveIntegral.value T (lossBound N) TorusFlight.flight f₀
        (fun w => positiveSource N (fun p => F (w.1,p)) w.2) z := by
  obtain ⟨f,hf⟩ := exists_weighted_cutoff_solution hN hT hfm hf₀
  let F : ℝ × Phase → ℝ := fun z => Real.exp (scalingRate N*PositiveIntegral.time T z.1)*f.val z
  have hFm : Measurable F := by
    apply Measurable.mul _ (BoundedMeasurable.measurable (ℝ × Phase) f.val)
    unfold PositiveIntegral.time
    fun_prop
  refine ⟨F,hFm,?_,?_⟩
  · intro z
    refine ⟨mul_nonneg (Real.exp_pos _).le (f.property z).1,?_⟩
    have he : Real.exp (scalingRate N*PositiveIntegral.time T z.1) ≤ Real.exp (scalingRate N*T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (PositiveIntegral.time_bounds hT z.1).2
        (scalingRate_pos hN).le)
    exact mul_le_mul he (f.property z).2 (f.property z).1 (Real.exp_pos _).le
  · intro z
    have h := congrArg (fun r => Real.exp (scalingRate N*PositiveIntegral.time T z.1)*r) (hf z)
    change F z = _ at h
    have hs : scaledSource T (scalingRate N) N (fun z => f.val z) =
        (fun w => Real.exp (-scalingRate N*PositiveIntegral.time T w.1)*
          positiveSource N (fun p => F (w.1,p)) w.2) := by
      funext w
      exact scaledSource_eq _ _ _ _ _
    rw [hs] at h
    simpa only [dampingRate,PositiveIntegral.value_rescale hT] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
