import Mathlib
import OAI.Analysis.Conductivity.Scalarization.SmoothScalarAlgebra

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

def smoothPrimitive (h : SmoothScalar ℝ) : SmoothScalar ℝ :=
  ⟨fun x => ∫ t in (0 : ℝ)..x, h.val t, by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) _
    have hd : ∀ x : ℝ, HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, h.val t) (h.val x) x :=
      fun x => intervalIntegral.integral_hasDerivAt_right
        ((smoothScalar_contDiff h).continuous.intervalIntegrable 0 x)
        ((smoothScalar_contDiff h).continuous.stronglyMeasurableAtFilter _ _)
        (smoothScalar_contDiff h).continuous.continuousAt
    exact contDiff_infty_iff_deriv.mpr
      ⟨fun x => (hd x).differentiableAt, by
        rw [deriv_eq hd]
        exact smoothScalar_contDiff h⟩⟩

@[simp] theorem smoothDirection_smoothPrimitive (h : SmoothScalar ℝ) :
    smoothDirection 1 (smoothPrimitive h) = h := by
  apply Subtype.ext
  funext x
  change deriv (fun x => ∫ t in (0 : ℝ)..x, h.val t) x = h.val x
  exact (intervalIntegral.integral_hasDerivAt_right
    ((smoothScalar_contDiff h).continuous.intervalIntegrable 0 x)
    ((smoothScalar_contDiff h).continuous.stronglyMeasurableAtFilter _ _)
    (smoothScalar_contDiff h).continuous.continuousAt).deriv

def meanZeroPrimitive (h : SmoothScalar ℝ) : SmoothScalar ℝ :=
  smoothPrimitive h - algebraMap ℝ (SmoothScalar ℝ)
    (∫ t in (0 : ℝ)..1, (smoothPrimitive h).val t)

@[simp] theorem smoothDirection_meanZeroPrimitive (h : SmoothScalar ℝ) :
    smoothDirection 1 (meanZeroPrimitive h) = h := by
  rw [meanZeroPrimitive, map_sub, smoothDirection_smoothPrimitive]
  have hc (c : ℝ) : smoothDirection (1 : ℝ)
      (algebraMap ℝ (SmoothScalar ℝ) c) = 0 := by
    apply Subtype.ext
    funext x
    change fderiv ℝ (fun _ : ℝ => c) x 1 = 0
    simp
  rw [hc, sub_zero]

theorem meanZeroPrimitive_mean (h : SmoothScalar ℝ) :
    ∫ t in (0 : ℝ)..1, (meanZeroPrimitive h).val t = 0 := by
  change (∫ t in (0 : ℝ)..1, (smoothPrimitive h).val t -
    ∫ s in (0 : ℝ)..1, (smoothPrimitive h).val s) = 0
  rw [intervalIntegral.integral_sub
    ((smoothScalar_contDiff (smoothPrimitive h)).continuous.intervalIntegrable _ _)
    (intervalIntegrable_const)]
  simp [intervalIntegral.integral_const]

theorem meanZeroPrimitive_periodic (h : SmoothScalar ℝ)
    (hp : Function.Periodic h.val 1) (hm : ∫ t in (0 : ℝ)..1, h.val t = 0) :
    Function.Periodic (meanZeroPrimitive h).val 1 := by
  intro x
  change (∫ t in (0 : ℝ)..x + 1, h.val t) -
    (∫ t in (0 : ℝ)..1, (smoothPrimitive h).val t) =
    (∫ t in (0 : ℝ)..x, h.val t) -
    (∫ t in (0 : ℝ)..1, (smoothPrimitive h).val t)
  rw [hp.intervalIntegral_add_eq_add 0 x
    (fun a b => (smoothScalar_contDiff h).continuous.intervalIntegrable a b)]
  simp only [zero_add, hm, add_zero]

theorem periodic_smoothScalar_bounded (h : SmoothScalar ℝ)
    (hp : Function.Periodic h.val 1) : ∃ C : ℝ, ∀ t, |h.val t| ≤ C := by
  obtain ⟨C, hC⟩ :=
    (hp.isBounded_of_continuous one_ne_zero (smoothScalar_contDiff h).continuous).exists_norm_le
  exact ⟨C, fun t => by simpa only [Real.norm_eq_abs] using hC _ ⟨t, rfl⟩⟩

theorem periodic_two_primitives (h : SmoothScalar ℝ)
    (hp : Function.Periodic h.val 1) (hm : ∫ t in (0 : ℝ)..1, h.val t = 0) :
    ∃ H₁ H₂ : SmoothScalar ℝ,
      smoothDirection 1 H₁ = h ∧ smoothDirection 1 H₂ = H₁ ∧
      Function.Periodic H₁.val 1 ∧ Function.Periodic H₂.val 1 ∧
      (∃ C : ℝ, ∀ t, |H₁.val t| ≤ C) ∧
      (∃ C : ℝ, ∀ t, |H₂.val t| ≤ C) := by
  let H₁ := meanZeroPrimitive h
  let H₂ := meanZeroPrimitive H₁
  have hp₁ : Function.Periodic H₁.val 1 := meanZeroPrimitive_periodic h hp hm
  have hp₂ : Function.Periodic H₂.val 1 :=
    meanZeroPrimitive_periodic H₁ hp₁ (meanZeroPrimitive_mean h)
  exact ⟨H₁, H₂, smoothDirection_meanZeroPrimitive h,
    smoothDirection_meanZeroPrimitive H₁, hp₁, hp₂,
    periodic_smoothScalar_bounded H₁ hp₁, periodic_smoothScalar_bounded H₂ hp₂⟩

end ScalarConductivity

end

end OAI
