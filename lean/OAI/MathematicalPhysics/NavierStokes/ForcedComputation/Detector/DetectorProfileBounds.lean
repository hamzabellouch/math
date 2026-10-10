import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EffectiveProfiles
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Extension
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.PeriodicExpressions
import Mathlib.Analysis.Calculus.Deriv.Support

namespace OAI

/-! Computed natural-number bounds for the fixed bump profile. These give
the width-independent constants used before rescaling detector injections. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set

def baseDetectorProfile : ProfileExpr := ProfileExpr.cutoff (-1) (-1 / 2) (1 / 2) 1

def detectorProfileDerivativeBound (n : ℕ) : ℕ :=
  ⌈(baseDetectorProfile.diffN n).bound 1⌉₊ + 1

theorem baseDetectorProfile_support (n : ℕ) :
    tsupport (iteratedDeriv n baseDetectorProfile.val) ⊆ Icc (-1 : ℝ) 1 := by
  induction n with
  | zero =>
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have he : baseDetectorProfile.val = closedCutoff (-1) (-1 / 2) (1 / 2) 1 := by
      simpa only [baseDetectorProfile, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using
        ProfileExpr.val_cutoff (-1) (-1 / 2) (1 / 2) 1
    change baseDetectorProfile.val x ≠ 0 at hx
    rw [he] at hx
    exact Ioo_subset_Icc_self (closedCutoff_support (by norm_num : (-1 : ℝ) < -1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hx)
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem baseDetectorProfile_derivative_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n baseDetectorProfile.val x| ≤ (detectorProfileDerivativeBound n : ℝ) := by
  by_cases hx : |x| ≤ 1
  · rw [← ProfileExpr.val_diffN]
    have hb := (baseDetectorProfile.diffN n).val_bound (M := 1) (by simpa using hx)
    apply hb.trans
    have hc : ((baseDetectorProfile.diffN n).bound 1 : ℝ) ≤
        (⌈(baseDetectorProfile.diffN n).bound 1⌉₊ : ℝ) := by
      exact_mod_cast Nat.le_ceil ((baseDetectorProfile.diffN n).bound 1)
    simp only [detectorProfileDerivativeBound, Nat.cast_add, Nat.cast_one]
    linarith
  · have hnot : x ∉ Icc (-1 : ℝ) 1 := by
      intro h
      exact hx (abs_le.mpr h)
    have hz : iteratedDeriv n baseDetectorProfile.val x = 0 := by
      by_contra hn
      exact hnot (baseDetectorProfile_support n (subset_closure hn))
    rw [hz, abs_zero]
    exact Nat.cast_nonneg _

end ForcedComputation.VelocityDetector

end

end OAI
