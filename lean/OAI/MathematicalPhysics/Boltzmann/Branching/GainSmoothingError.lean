import OAI.MathematicalPhysics.Boltzmann.Branching.HotQuadraticGain
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionMeasure
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocitySmoothingError
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformGainTranslation

namespace OAI

section

/-! # The weighted gain difference estimate for finite approximations -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GainLipschitz

theorem integrand_difference {f g : Velocity → ℝ} {q A B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, |f w - g w| ≤ D * H q w) (v : Velocity) (p : Velocity × Sphere) :
    |GainOrder.integrand f v p - GainOrder.integrand g v p| ≤
      (D * (A + B)) * GainOrder.integrand (H q) v p := by
  let l := scatterLeft v p.1 p.2
  let r := scatterRight v p.1 p.2
  have h1 := mul_le_mul (hfg l) (hfB r) (hf r) (mul_nonneg hD (H_nonneg q l))
  have h2 := mul_le_mul (hgB l) (hfg r) (abs_nonneg (f r - g r))
    (mul_nonneg hB (H_nonneg q l))
  have hp : |(f l - g l) * f r + g l * (f r - g r)| ≤
      (D * H q l) * (A * H q r) + (B * H q l) * (D * H q r) := by
    calc
      _ ≤ |(f l - g l) * f r| + |g l * (f r - g r)| := abs_add_le _ _
      _ = |f l - g l| * f r + g l * |f r - g r| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hf r), abs_of_nonneg (hg l)]
      _ ≤ _ := add_le_add h1 h2
  have he : GainOrder.integrand f v p - GainOrder.integrand g v p =
      collisionKernel v p.1 p.2 * ((f l - g l) * f r + g l * (f r - g r)) := by
    unfold GainOrder.integrand l r
    ring
  rw [he, abs_mul, abs_of_nonneg (collisionKernel_nonneg _ _ _)]
  calc
    _ ≤ collisionKernel v p.1 p.2 *
        ((D * H q l) * (A * H q r) + (B * H q l) * (D * H q r)) :=
      mul_le_mul_of_nonneg_left hp (collisionKernel_nonneg _ _ _)
    _ = _ := by unfold GainOrder.integrand l r; ring

theorem gain_difference (hcarleman : Published.GPV2009CarlemanInput)
    {q A B D : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, |f w - g w| ≤ D * H q w) :
    ∀ᵐ v : Velocity, ∀ x : Position,
      |gain (fun p => f p.2) x v - gain (fun p => g p.2) x v| ≤
        (D * (A + B) * HotApplication.realBound q) * H q v := by
  filter_upwards [HotRealGain.quadratic_gain hcarleman hq₁ hq₂] with v hv
  have hfi := GainOrder.integrable_of_le hfm hf hfB v (GainOrder.integrable_const_mul A v hv.1)
  have hgi := GainOrder.integrable_of_le hgm hg hgB v (GainOrder.integrable_const_mul B v hv.1)
  have habs : Integrable (fun p => |GainOrder.integrand f v p - GainOrder.integrand g v p|)
      ((volume : Measure Velocity).prod sphereArea) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hfi.sub hgi).norm
  intro x
  calc
    _ = |∫ p, GainOrder.integrand f v p - GainOrder.integrand g v p
        ∂((volume : Measure Velocity).prod sphereArea)| := by
      rw [integral_sub hfi hgi]
      rfl
    _ ≤ ∫ p, |GainOrder.integrand f v p - GainOrder.integrand g v p|
        ∂((volume : Measure Velocity).prod sphereArea) := abs_integral_le_integral_abs
    _ ≤ ∫ p, (D * (A + B)) * GainOrder.integrand (H q) v p
        ∂((volume : Measure Velocity).prod sphereArea) :=
      integral_mono habs (hv.1.const_mul _) (integrand_difference hB hD hf hg hfB hgB hfg v)
    _ = (D * (A + B)) * gain (fun p => H q p.2) x v := integral_const_mul _ _
    _ ≤ (D * (A + B)) * (HotApplication.realBound q * H q v) :=
      mul_le_mul_of_nonneg_left (hv.2 x) (mul_nonneg hD (add_nonneg hA hB))
    _ = _ := by ring

end BoltzmannNonuniqueness.GainLipschitz

end

end

section

/-! # One-sided gain differences for the nonlinear cold comparison -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GainUpperDifference

theorem integrand_bound {f g : Velocity → ℝ} {q A B D : ℝ} (hD : 0 ≤ D)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, f w - g w ≤ D * H q w) (v : Velocity) (p : Velocity × Sphere) :
    GainOrder.integrand f v p - GainOrder.integrand g v p ≤
      (D * (A + B)) * GainOrder.integrand (H q) v p := by
  let l := scatterLeft v p.1 p.2
  let r := scatterRight v p.1 p.2
  have h1 : (f l - g l) * f r ≤ (D * H q l) * (A * H q r) :=
    (mul_le_mul_of_nonneg_right (hfg l) (hf r)).trans
      (mul_le_mul_of_nonneg_left (hfB r) (mul_nonneg hD (H_nonneg q l)))
  have h2 : g l * (f r - g r) ≤ (B * H q l) * (D * H q r) :=
    (mul_le_mul_of_nonneg_left (hfg r) (hg l)).trans
      (mul_le_mul_of_nonneg_right (hgB l) (mul_nonneg hD (H_nonneg q r)))
  have he : GainOrder.integrand f v p - GainOrder.integrand g v p =
      collisionKernel v p.1 p.2 * ((f l - g l) * f r + g l * (f r - g r)) := by
    unfold GainOrder.integrand l r
    ring
  rw [he]
  calc
    _ ≤ collisionKernel v p.1 p.2 *
        ((D * H q l) * (A * H q r) + (B * H q l) * (D * H q r)) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) (collisionKernel_nonneg _ _ _)
    _ = _ := by unfold GainOrder.integrand l r; ring

theorem cutoff_integrand_bound {f g : Velocity → ℝ} {q A B D : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, f w - g w ≤ D * H q w) (b : ℝ) (v : Velocity) (p : Velocity × Sphere) :
    CollisionCutoff.integrand b f v p - CollisionCutoff.integrand b g v p ≤
      (D * (A + B)) * GainOrder.integrand (H q) v p := by
  by_cases hp : ‖v - p.1‖ < b
  · simpa only [CollisionCutoff.integrand, CollisionCutoff.kernel, GainOrder.integrand, ite_eq_left hp] using
      integrand_bound hD hf hg hfB hgB hfg v p
  · simp only [CollisionCutoff.integrand, CollisionCutoff.kernel, ite_eq_right hp, zero_mul, sub_self]
    exact mul_nonneg (mul_nonneg hD (add_nonneg hA hB)) (GainOrder.integrand_nonneg (H_nonneg q) v p)

/-- Only the positive difference of the two densities enters the upper gain difference. -/
theorem cutoff_gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {q A B D : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, f w - g w ≤ D * H q w) (b : ℝ) :
    ∀ᵐ v : Velocity,
      CollisionCutoff.gain b f v - CollisionCutoff.gain b g v ≤
        (D * (A + B) * HotApplication.realBound q) * H q v := by
  filter_upwards [HotRealGain.quadratic_gain hcarleman hq₁ hq₂] with v hv
  have hfi := GainOrder.integrable_of_le hfm hf hfB v (GainOrder.integrable_const_mul A v hv.1)
  have hgi := GainOrder.integrable_of_le hgm hg hgB v (GainOrder.integrable_const_mul B v hv.1)
  have hfc := CollisionCutoff.integrable_gain b hfm hf v hfi
  have hgc := CollisionCutoff.integrable_gain b hgm hg v hgi
  calc
    _ = ∫ p, CollisionCutoff.integrand b f v p - CollisionCutoff.integrand b g v p
        ∂((volume : Measure Velocity).prod sphereArea) := (integral_sub hfc hgc).symm
    _ ≤ ∫ p, (D * (A + B)) * GainOrder.integrand (H q) v p
        ∂((volume : Measure Velocity).prod sphereArea) :=
      integral_mono (hfc.sub hgc) (hv.1.const_mul _)
        (cutoff_integrand_bound hA hB hD hf hg hfB hgB hfg b v)
    _ = (D * (A + B)) * gain (fun p => H q p.2) 0 v := integral_const_mul _ _
    _ ≤ (D * (A + B)) * (HotApplication.realBound q * H q v) :=
      mul_le_mul_of_nonneg_left (hv.2 0) (mul_nonneg hD (add_nonneg hA hB))
    _ = _ := by ring

end BoltzmannNonuniqueness.GainUpperDifference

end

end

section

/-! # A common L1 smoothing error for the actual localized gain sequence -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

omit [MeasurableSpace X] in
theorem velocitySmooth_eq_outgoing_convolution (χ : Velocity → ℝ)
    (F : X × Velocity → ℝ) (p : X × Velocity) :
    velocitySmooth χ F p = ∫ u : Velocity, χ (p.2-u)*F (p.1,u) := by
  have h := integral_sub_left_eq_self (fun u : Velocity => χ u*F (p.1,p.2-u)) volume p.2
  change (∫ u : Velocity, χ u*F (p.1,p.2-u)) = _
  simpa only [sub_sub_cancel] using h.symm

theorem localizedGain_uniform_smoothing
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (η : C(Velocity,ℝ)) (hη : HasCompactSupport η) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ χ : Velocity → ℝ,
      Integrable χ → (∀ a, 0 ≤ χ a) → (∫ a, χ a) = 1 →
      (∀ a, χ a ≠ 0 → ‖a‖ < δ) → ∀ n,
      (∫ p, |velocitySmooth χ (localizedPhysicalGain η (f n)) p-
        localizedPhysicalGain η (f n) p| ∂μ.prod volume) ≤ ε := by
  obtain ⟨δ,hδ,hsmall⟩ := localizedGain_uniform_translation hfm hf hi hb η hη ε hε
  refine ⟨δ,hδ,fun χ hχ hχ0 hmass hs n => ?_⟩
  have hwi : Integrable (weightedNormalizedPair (f n))
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
    simpa only [Measure.volume_eq_prod] using weightedNormalizedPair_integrable (hfm n) (hf n) (hi n)
  apply velocitySmooth_error_le hχ (localizedPhysicalGain_integrable η hη (hfm n) hwi) hχ0 hmass
  intro a ha
  have hs' : ‖-a‖ < δ := by simpa only [norm_neg] using hs a ha
  have ht := (hsmall n (-a) hs').le
  simpa only [sub_eq_add_neg] using ht

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
