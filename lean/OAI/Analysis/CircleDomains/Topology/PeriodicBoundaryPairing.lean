import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace OAI

/-! A boundary pairing defined for continuous lifts is stable under
uniform perturbations of the same period. For smooth lifts it is the
ordinary boundary integral, by integration by parts. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def liftedBoundaryPairing (φ dφ v : ℝ → ℝ) : ℝ :=
  φ 1 * v 1 - φ 0 * v 0 - ∫ x in (0 : ℝ)..1, dφ x * v x

theorem liftedBoundaryPairing_eq_integral
    (φ dφ v dv : ℝ → ℝ)
    (hφ : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt φ (dφ x) x)
    (hv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt v (dv x) x)
    (hdφ : IntervalIntegrable dφ volume 0 1)
    (hdv : IntervalIntegrable dv volume 0 1) :
    liftedBoundaryPairing φ dφ v = ∫ x in (0 : ℝ)..1, φ x * dv x :=
  (intervalIntegral.integral_mul_deriv_eq_deriv_mul hφ hv hdφ hdv).symm

theorem liftedBoundaryPairing_stability
    (φ dφ u v : ℝ → ℝ) (hφ : φ 1 = φ 0)
    (hperiod : u 1 - u 0 = v 1 - v 0)
    (hu : ContinuousOn u (Icc (0 : ℝ) 1))
    (hv : ContinuousOn v (Icc (0 : ℝ) 1))
    (hdφ : IntervalIntegrable dφ volume 0 1)
    (δ : ℝ) (hclose : ∀ x ∈ Icc (0 : ℝ) 1, |u x - v x| ≤ δ) :
    |liftedBoundaryPairing φ dφ u - liftedBoundaryPairing φ dφ v| ≤
      δ * ∫ x in (0 : ℝ)..1, |dφ x| := by
  have hu' : ContinuousOn u (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hu
  have hv' : ContinuousOn v (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hv
  have hdu := hdφ.mul_continuousOn hu'
  have hdv := hdφ.mul_continuousOn hv'
  have hi : (∫ x in (0 : ℝ)..1, dφ x * (u x - v x)) =
      (∫ x in (0 : ℝ)..1, dφ x * u x) - ∫ x in (0 : ℝ)..1, dφ x * v x := by
    simp_rw [mul_sub]
    exact intervalIntegral.integral_sub hdu hdv
  have he : liftedBoundaryPairing φ dφ u - liftedBoundaryPairing φ dφ v =
      -(∫ x in (0 : ℝ)..1, dφ x * (u x - v x)) := by
    unfold liftedBoundaryPairing
    rw [hi, hφ]
    have hp := congrArg (fun t : ℝ => φ 0 * t) hperiod
    nlinarith only [hp]
  have hw : IntervalIntegrable (fun x => δ * |dφ x|) volume 0 1 := by
    simpa only [Real.norm_eq_abs] using hdφ.norm.const_mul δ
  have hb : ‖∫ x in (0 : ℝ)..1, dφ x * (u x - v x)‖ ≤
      ∫ x in (0 : ℝ)..1, δ * |dφ x| := by
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one _ hw
    apply Eventually.of_forall
    intro x hx
    simp only [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left (hclose x ⟨hx.1.le, hx.2⟩) (abs_nonneg _)).trans_eq
      (mul_comm _ _)
  rw [he, abs_neg]
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul] using hb

end CircleDomainRigidity

end

end OAI
