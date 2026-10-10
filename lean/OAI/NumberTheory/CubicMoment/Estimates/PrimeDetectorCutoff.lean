import OAI.NumberTheory.CubicMoment.Estimates.PrimeDetector
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

/-! An explicit smooth cutoff for the exact prime detector. -/
noncomputable section
open Filter
open scoped ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primeDetectorCutoff (x : ℝ) : ℝ := 1-Real.smoothTransition (x-1)

lemma primeDetectorCutoff_nonneg (x : ℝ) : 0 ≤ primeDetectorCutoff x :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

lemma primeDetectorCutoff_le_one (x : ℝ) : primeDetectorCutoff x ≤ 1 := by
  unfold primeDetectorCutoff
  linarith [Real.smoothTransition.nonneg (x-1)]

lemma primeDetectorCutoff_one {x : ℝ} (hx : x ≤ 1) : primeDetectorCutoff x = 1 := by
  rw [primeDetectorCutoff,Real.smoothTransition.zero_of_nonpos (by linarith),sub_zero]

lemma primeDetectorCutoff_zero {x : ℝ} (hx : 2 ≤ x) : primeDetectorCutoff x = 0 := by
  rw [primeDetectorCutoff,Real.smoothTransition.one_of_one_le (by linarith),sub_self]

lemma primeDetectorCutoff_smooth : ContDiff ℝ ∞ primeDetectorCutoff :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem concrete_prime_detector {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ X : ℝ in atTop, ∀ (S : Finset Eisenstein) (K : Eisenstein → ℂ),
      (∀ n ∈ S, c*X ≤ norm n ∧ norm n ≤ C*X) →
      (∀ n ∈ S, ¬Squarefree n → K n = 0) →
      (∑ n ∈ S with Prime n, K n) =
        (∑ n ∈ S, (roughProduct primeDetectorCutoff (X^(2/5:ℝ)) n:ℂ)*K n) -
          ∑ n ∈ S with (primeFactors n).card = 2,
            (roughProduct primeDetectorCutoff (X^(2/5:ℝ)) n:ℂ)*K n :=
  prime_detector_finite_envelope hc hC (fun _ _ hx => primeDetectorCutoff_one hx)
    (fun _ hx => primeDetectorCutoff_zero hx)

end CubicFirstMoment

end

end OAI
