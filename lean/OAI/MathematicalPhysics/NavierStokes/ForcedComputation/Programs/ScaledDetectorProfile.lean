import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorProfileBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodizeBound
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorBump

namespace OAI

/-! Width-independent derivative constants for the periodized detector
profile, with the exact inverse-width scaling in each derivative. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

def scaledDetectorProfile (b : ℝ) (x : ℝ) : ℝ :=
  baseDetectorProfile.val ((x - 1 / 4) / b)

theorem scaledDetectorProfile_smooth (b : ℝ) : ContDiff ℝ ∞ (scaledDetectorProfile b) :=
  baseDetectorProfile.smooth.comp ((contDiff_id.sub contDiff_const).div_const b)

theorem scaledDetectorProfile_eq {b : ℝ} (hb : 0 < b) (x : ℝ) :
    scaledDetectorProfile b x =
      closedCutoff (1 / 4 - b) (1 / 4 - b / 2) (1 / 4 + b / 2) (1 / 4 + b) x := by
  have he : baseDetectorProfile.val = closedCutoff (-1) (-1 / 2) (1 / 2) 1 := by
    simpa only [baseDetectorProfile, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using
      ProfileExpr.val_cutoff (-1) (-1 / 2) (1 / 2) 1
  unfold scaledDetectorProfile
  rw [he]
  have hd₁ : (1 / 4 - b / 2) - (1 / 4 - b) = b / 2 := by ring
  have hd₂ : -(1 / 4 + b / 2) - -(1 / 4 + b) = b / 2 := by ring
  simp only [closedCutoff, smoothRamp, hd₁, hd₂]
  apply congrArg₂ (· * ·)
  · apply congrArg Real.smoothTransition
    field_simp [hb.ne']
    ring
  · apply congrArg Real.smoothTransition
    field_simp [hb.ne']
    ring

theorem scaledDetectorProfile_iteratedDeriv {b : ℝ} (_hb : 0 < b) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (scaledDetectorProfile b) x =
      b⁻¹ ^ n * iteratedDeriv n baseDetectorProfile.val ((x - 1 / 4) / b) := by
  have he : scaledDetectorProfile b =
      fun x => (fun z => baseDetectorProfile.val (b⁻¹ * z)) (x - 1 / 4) := by
    funext x
    simp only [scaledDetectorProfile, div_eq_mul_inv, mul_comm]
  rw [he, iteratedDeriv_comp_sub_const n (fun z => baseDetectorProfile.val (b⁻¹ * z)) (1 / 4),
    iteratedDeriv_comp_const_mul (n := n) (baseDetectorProfile.smooth.of_le (by simp)) b⁻¹]
  simp only [div_eq_mul_inv, mul_comm]

theorem scaledDetectorProfile_derivative_bound {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (scaledDetectorProfile b) x| ≤
      b⁻¹ ^ n * (detectorProfileDerivativeBound n : ℝ) := by
  rw [scaledDetectorProfile_iteratedDeriv hb, abs_mul,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hb.le) n)]
  exact mul_le_mul_of_nonneg_left (baseDetectorProfile_derivative_bound n _)
    (pow_nonneg (inv_nonneg.mpr hb.le) n)

theorem scaledDetectorProfile_support {b : ℝ} (hb : 0 < b) :
    Function.support (scaledDetectorProfile b) ⊆ Icc (1 / 4 - b) (1 / 4 + b) := by
  intro x hx
  have he := baseDetectorProfile_support 0
    (subset_closure (show baseDetectorProfile.val ((x - 1 / 4) / b) ≠ 0 from hx))
  have hlo := (le_div_iff₀ hb).mp he.1
  have hhi := (div_le_iff₀ hb).mp he.2
  constructor <;> linarith

theorem detectorProfile_eq_periodize_scaled {b : ℝ} (hb : 0 < b) :
    detectorProfile b = periodize 1 (scaledDetectorProfile b) := by
  unfold detectorProfile circleCutoff
  congr 1
  funext x
  exact (scaledDetectorProfile_eq hb x).symm

theorem detectorProfile_iteratedDeriv_bound {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1 / 16)
    (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (detectorProfile b) x| ≤
      b⁻¹ ^ n * (detectorProfileDerivativeBound n : ℝ) := by
  rw [detectorProfile_eq_periodize_scaled hb,
    periodize_iteratedDeriv (scaledDetectorProfile_smooth b) (scaledDetectorProfile_support hb)]
  exact periodize_unit_bound
    (iteratedDeriv_support_interval (scaledDetectorProfile_support hb) n)
    (by linarith) (by positivity) (scaledDetectorProfile_derivative_bound hb n) x

end ForcedComputation.VelocityDetector

end

end OAI
