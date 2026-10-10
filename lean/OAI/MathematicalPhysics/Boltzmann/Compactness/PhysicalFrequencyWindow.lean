import OAI.MathematicalPhysics.Boltzmann.Branching.LossIntegrability
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals
import OAI.MathematicalPhysics.Boltzmann.Collision.FourierCompactness
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocitySmoothingError

namespace OAI

section

/-! # Physical loss frequency in kinetic spacetime coordinates -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def kineticFrequency (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  2*Real.pi*∫ w, ‖p.2-w‖*f (p.1,w)

theorem kineticFrequency_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (kineticFrequency f) := by
  have hm : Measurable (fun p : (X × Velocity) × Velocity => ‖p.1.2-p.2‖*f (p.1.1,p.2)) := by
    fun_prop
  exact measurable_const.mul hm.stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableSpace X] in
theorem kineticFrequency_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (p : X × Velocity) : 0 ≤ kineticFrequency f p := by
  unfold kineticFrequency
  exact mul_nonneg (by positivity) (integral_nonneg (fun w => mul_nonneg (norm_nonneg _) (hf _)))

theorem lossDensity_eq_mul_kineticFrequency (f : X × Velocity → ℝ) (p : X × Velocity)
    (hi : Integrable (fun q : Velocity × Sphere => preRate f (collisionGrouping.symm (p,q)))
      ((volume : Measure Velocity).prod sphereArea)) :
    lossDensity f p = f p*kineticFrequency f p := by
  change Integrable (fun q : Velocity × Sphere =>
    collisionKernel p.2 q.1 q.2*f (p.1,p.2)*f (p.1,q.1)) _ at hi
  rw [lossDensity_formula,integral_prod _ hi]
  simp_rw [integral_mul_const,integral_collisionKernel_sphereArea]
  calc
    (∫ w, 2*Real.pi*‖p.2-w‖*f (p.1,p.2)*f (p.1,w)) =
        ∫ w, (f p*(2*Real.pi))*(‖p.2-w‖*f (p.1,w)) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun w => by dsimp; ring)
    _ = (f p*(2*Real.pi))*(∫ w, ‖p.2-w‖*f (p.1,w)) := integral_const_mul _ _
    _ = f p*kineticFrequency f p := by unfold kineticFrequency; ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Physical spacetime frequencies in the velocity spectral estimate -/
noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

def physicalFourierFrequency (k : FourierSpace) : SpaceTime :=
  (2*Real.pi) • WithLp.ofLp k

theorem physicalFourierMultiplier (k : FourierSpace) (v : Velocity) :
    complexVelocityMultiplier 1 (physicalFourierFrequency k) v =
      (1+Complex.I*(2*Real.pi*inner ℝ (characteristicDirection v) k))⁻¹ := by
  rw [real_inner_comm k (characteristicDirection v),characteristicFrequency]
  simp only [complexVelocityMultiplier,physicalFourierFrequency,Prod.smul_fst,
    Prod.smul_snd,smul_eq_mul,real_inner_smul_left,Nat.cast_one]
  push_cast
  ring_nf

theorem velocity_spectral_integral_bound (R : ℝ) (k : SpaceTime)
    {f : Velocity → ℂ} (hf : MemLp f 2 (volume.restrict (Metric.closedBall (0 : Velocity) R))) :
    ‖∫ v in Metric.closedBall (0 : Velocity) R, complexVelocityMultiplier 1 k v*f v‖^2 ≤
      velocityMultiplierMass R 1 k * ∫ v in Metric.closedBall (0 : Velocity) R, ‖f v‖^2 := by
  let a := hf.toLp f
  have h₁ : (∫ v in Metric.closedBall (0 : Velocity) R, complexVelocityMultiplier 1 k v*f v) =
      ∫ v in Metric.closedBall (0 : Velocity) R, complexVelocityMultiplier 1 k v*a v := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with v hv
    rw [hv]
  have h₂ : (∫ v in Metric.closedBall (0 : Velocity) R, ‖f v‖^2) = ‖a‖^2 := by
    rw [L2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with v hv
    rw [hv]
  rw [h₁,h₂]
  exact velocity_spectral_bound R 1 k a

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Finite Fourier windows for the physical spacetime coordinates -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

theorem physicalFourierFrequency_continuous : Continuous physicalFourierFrequency := by
  unfold physicalFourierFrequency
  fun_prop

theorem norm_le_physicalFourierFrequency (k : FourierSpace) :
    ‖k‖ ≤ ‖physicalFourierFrequency k‖ := by
  have h₁ : ‖(WithLp.ofLp k).1‖ ≤ ‖WithLp.ofLp k‖ := norm_fst_le _
  have h₂ : ‖(WithLp.ofLp k).2‖ ≤ ‖WithLp.ofLp k‖ := norm_snd_le _
  have hs := WithLp.prod_norm_sq_eq_of_L2 k
  change ‖k‖^2 = ‖(WithLp.ofLp k).1‖^2+‖(WithLp.ofLp k).2‖^2 at hs
  have hs₁ := pow_le_pow_left₀ (norm_nonneg (WithLp.ofLp k).1) h₁ 2
  have hs₂ := pow_le_pow_left₀ (norm_nonneg (WithLp.ofLp k).2) h₂ 2
  have hb : ‖k‖ ≤ 2*‖WithLp.ofLp k‖ := by
    nlinarith [norm_nonneg k,norm_nonneg (WithLp.ofLp k),norm_nonneg (WithLp.ofLp k).1,
      norm_nonneg (WithLp.ofLp k).2]
  rw [physicalFourierFrequency,norm_smul,Real.norm_of_nonneg (by positivity)]
  nlinarith [Real.pi_gt_three,norm_nonneg (WithLp.ofLp k)]

def physicalFrequencyWindow (N : ℕ) : Set FourierSpace :=
  {k | ‖physicalFourierFrequency k‖ ≤ N}

theorem physicalFrequencyWindow_measurable (N : ℕ) : MeasurableSet (physicalFrequencyWindow N) :=
  (isClosed_Iic.preimage physicalFourierFrequency_continuous.norm).measurableSet

theorem physicalFrequencyWindow_finite (N : ℕ) : volume (physicalFrequencyWindow N) < ⊤ := by
  apply lt_of_le_of_lt (measure_mono (t := Metric.closedBall (0 : FourierSpace) N) ?_)
    (isCompact_closedBall _ _).measure_lt_top
  intro k hk
  exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using
    (norm_le_physicalFourierFrequency k).trans hk)

end BoltzmannNonuniqueness.Published

end

end

end OAI
