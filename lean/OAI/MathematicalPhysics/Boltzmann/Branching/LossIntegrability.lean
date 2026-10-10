import OAI.MathematicalPhysics.Boltzmann.Collision.AngularPairTests

namespace OAI

section

/-!
# Loss frequency and its first-moment bound

The angular normalization gives the loss-frequency formula from Section 2,
equation `eq:frequency`. Fubini is used only with an explicit integrability
hypothesis for the original collision integrand. Separate first-moment
conditions ensure that the frequency integral itself is finite.
-/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

/-- The loss frequency in the paper's normal parametrization. -/
def frequency (f : Density) (x : Position) (v : Velocity) : ℝ :=
  2 * Real.pi * ∫ w : Velocity, ‖v - w‖ * f (x, w)

/-- Fubini and angular normalization identify the original loss collision integral. -/
theorem loss_eq_mul_frequency (f : Density) (x : Position) (v : Velocity)
    (hi : Integrable (fun p : Velocity × Sphere =>
      collisionKernel v p.1 p.2 * f (x, v) * f (x, p.1))
      ((volume : Measure Velocity).prod sphereArea)) :
    loss f x v = f (x, v) * frequency f x v := by
  unfold loss
  rw [integral_prod _ hi]
  simp_rw [integral_mul_const, integral_collisionKernel_sphereArea]
  calc
    (∫ w : Velocity, 2 * Real.pi * ‖v - w‖ * f (x, v) * f (x, w)) =
        ∫ w : Velocity, (f (x, v) * (2 * Real.pi)) * (‖v - w‖ * f (x, w)) := by
      apply integral_congr_ae
      filter_upwards [] with w
      ring
    _ = (f (x, v) * (2 * Real.pi)) * (∫ w : Velocity, ‖v - w‖ * f (x, w)) :=
      integral_const_mul _ _
    _ = f (x, v) * frequency f x v := by rw [frequency]; ring

theorem frequency_integrand_norm_le (f : Density) (x : Position) (v w : Velocity) :
    ‖‖v - w‖ * f (x, w)‖ ≤
      ‖v‖ * |f (x, w)| + ‖w‖ * |f (x, w)| := by
  rw [Real.norm_eq_abs, abs_mul, abs_norm]
  calc
    ‖v - w‖ * |f (x, w)| ≤ (‖v‖ + ‖w‖) * |f (x, w)| :=
      mul_le_mul_of_nonneg_right (norm_sub_le v w) (abs_nonneg _)
    _ = _ := by ring

theorem integrable_abs_firstMoment (f : Density) (x : Position)
    (hm : Integrable (fun w : Velocity => ‖w‖ * f (x, w))) :
    Integrable (fun w : Velocity => ‖w‖ * |f (x, w)|) := by
  simpa only [Real.norm_eq_abs, abs_mul, abs_norm] using hm.norm

/-- Finite mass and first absolute velocity moment make the frequency integrable. -/
theorem integrable_frequency_integrand (f : Density) (x : Position) (v : Velocity)
    (hf : Integrable (fun w : Velocity => f (x, w)))
    (hm : Integrable (fun w : Velocity => ‖w‖ * f (x, w))) :
    Integrable (fun w : Velocity => ‖v - w‖ * f (x, w)) := by
  have hfa : Integrable (fun w : Velocity => |f (x, w)|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hb := (hfa.const_mul ‖v‖).add (integrable_abs_firstMoment f x hm)
  apply hb.mono' ((by fun_prop : AEStronglyMeasurable (fun w : Velocity => ‖v - w‖)).mul
    hf.aestronglyMeasurable)
  filter_upwards [] with w
  exact frequency_integrand_norm_le f x v w

/-- An absolute bound valid for signed densities as well as nonnegative ones. -/
theorem abs_frequency_le (f : Density) (x : Position) (v : Velocity)
    (hf : Integrable (fun w : Velocity => f (x, w)))
    (hm : Integrable (fun w : Velocity => ‖w‖ * f (x, w))) :
    |frequency f x v| ≤ 2 * Real.pi *
      (‖v‖ * (∫ w : Velocity, |f (x, w)|) +
        ∫ w : Velocity, ‖w‖ * |f (x, w)|) := by
  have hfa : Integrable (fun w : Velocity => |f (x, w)|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hma := integrable_abs_firstMoment f x hm
  have hi := integrable_frequency_integrand f x v hf hm
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  calc
    |frequency f x v| = 2 * Real.pi * |∫ w : Velocity, ‖v - w‖ * f (x, w)| := by
      rw [frequency, abs_mul, abs_of_nonneg hπ]
    _ ≤ 2 * Real.pi * (∫ w : Velocity, ‖‖v - w‖ * f (x, w)‖) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun w : Velocity => ‖v - w‖ * f (x, w))) hπ
    _ ≤ 2 * Real.pi * (∫ w : Velocity,
        ‖v‖ * |f (x, w)| + ‖w‖ * |f (x, w)|) := by
      apply mul_le_mul_of_nonneg_left _ hπ
      exact integral_mono_ae hi.norm ((hfa.const_mul ‖v‖).add hma)
        (Filter.Eventually.of_forall (frequency_integrand_norm_le f x v))
    _ = _ := by rw [integral_add (hfa.const_mul ‖v‖) hma, integral_const_mul]

theorem frequency_nonneg (f : Density) (x : Position) (v : Velocity)
    (hf : ∀ᵐ w : Velocity, 0 ≤ f (x, w)) : 0 ≤ frequency f x v := by
  unfold frequency
  apply mul_nonneg (by positivity)
  apply integral_nonneg_of_ae
  filter_upwards [hf] with w hw
  exact mul_nonneg (norm_nonneg _) hw

end BoltzmannNonuniqueness

end

end

section

/-! # Integrability of the original hard-sphere loss integral -/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem collisionKernel_le_norm (v w : Velocity) (ω : Sphere) :
    collisionKernel v w ω ≤ ‖v - w‖ := by
  have hω : ‖(ω : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  simpa only [collisionKernel, normalComponent, hω, mul_one] using
    abs_real_inner_le_norm (v - w) (ω : Velocity)

theorem integrable_loss_of_moments (f : Density) (x : Position) (v : Velocity)
    (hf : Integrable (fun w : Velocity => f (x, w)))
    (hm : Integrable (fun w : Velocity => ‖w‖ * f (x, w))) :
    Integrable (fun p : Velocity × Sphere =>
      collisionKernel v p.1 p.2 * f (x, v) * f (x, p.1))
      ((volume : Measure Velocity).prod sphereArea) := by
  have hi := ((integrable_frequency_integrand f x v hf hm).norm.const_mul |f (x, v)|).comp_fst sphereArea
  have hk : AEStronglyMeasurable (fun p : Velocity × Sphere => collisionKernel v p.1 p.2)
      ((volume : Measure Velocity).prod sphereArea) := by unfold collisionKernel normalComponent; fun_prop
  apply hi.mono' ((hk.mul aestronglyMeasurable_const).mul hf.aestronglyMeasurable.comp_fst)
  filter_upwards [] with p
  dsimp only [Pi.mul_apply]
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (collisionKernel_nonneg v p.1 p.2), abs_norm]
  calc
    collisionKernel v p.1 p.2 * |f (x, v)| * |f (x, p.1)| ≤
        ‖v - p.1‖ * |f (x, v)| * |f (x, p.1)| := by
      gcongr
      exact collisionKernel_le_norm v p.1 p.2
    _ = _ := by ring

theorem gaussian_gain_eq_frequency (A β : ℝ)
    (u : Velocity) (x : Position) (v : Velocity)
    (hf : Integrable (gaussian A β u))
    (hm : Integrable (fun w : Velocity => ‖w‖ * gaussian A β u w)) :
    gain (fun z => gaussian A β u z.2) x v =
      gaussian A β u v * frequency (fun z => gaussian A β u z.2) x v := by
  rw [gaussian_gain_eq_loss]
  exact loss_eq_mul_frequency (fun z => gaussian A β u z.2) x v
    (integrable_loss_of_moments (fun z => gaussian A β u z.2) x v hf hm)

end BoltzmannNonuniqueness

end

end

end OAI
