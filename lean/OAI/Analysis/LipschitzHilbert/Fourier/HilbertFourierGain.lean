import OAI.Analysis.LipschitzHilbert.Phase.FiniteFourierGain
import OAI.Analysis.LipschitzHilbert.Estimates.IntegralMinkowski

namespace OAI

/-! The diagonal finite-dimensional Hilbert version of the finite Fourier gain. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem diagonal_finite_fourier_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → κ → ℝ) (a : ι → κ → ℂ) {gap D p : ℝ}
    (hgap : 0 < gap) (hsep : ∀ j, Separated (fun i => frequency i j) gap)
    (hν : FourierGap ν gap) (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (hp : 4 ≤ p) :
    (∫ t, (∑ j, ‖finiteFourierSum (fun i => frequency i j) (fun i => a i j) t‖ ^ 2) ^
      (p / 2) ∂ν) ^ (1 / p) ≤
      (∑ i, (∑ j, ‖a i j‖ ^ 2) ^ (fourierInterpolationExponent D p / 2)) ^
        (1 / fourierInterpolationExponent D p) := by
  let F := fun j => finiteFourierSum (fun i => frequency i j) (fun i => a i j)
  let r := fourierInterpolationExponent D p
  let b := fun j => sequenceNorm (fun i => a i j) r
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := (fourier_interpolation_parameters hD hp).1
  have hθ := phaseParameter_range hD
  have hθ' : phaseParameter D ≤ 1 / 3 := hθ.2
  have hratio : (1 + phaseParameter D) / p ≤ 1 / 3 :=
    (div_le_iff₀ hp0).2 (by linarith)
  have hden : 0 < 1 - (1 + phaseParameter D) / p := by linarith
  have hr2 : r ≤ 2 := (div_le_iff₀ hden).2 (by linarith)
  have hscalar (j : κ) : (∫ t, ‖F j t‖ ^ p ∂ν) ^ (1 / p) ≤ b j :=
    finite_fourier_gain ν (fun i => frequency i j) (fun i => a i j)
      hgap (hsep j) hν hD hcard hp
  have hterm (j : κ) :
      (∫ t, (‖F j t‖ ^ 2) ^ (p / 2) ∂ν) ^ (1 / (p / 2)) ≤ b j ^ 2 := by
    have heq (t : ℝ) : (‖F j t‖ ^ 2) ^ (p / 2) = ‖F j t‖ ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      push_cast
      ring
    simp_rw [heq]
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg
      (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)) _) (hscalar j) 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul
      (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))] at hpow
    have he : (1 / p) * (2 : ℕ) = 1 / (p / 2) := by push_cast; field_simp
    rwa [he] at hpow
  have hsum := integral_finite_minkowski ν (fun j t => ‖F j t‖ ^ 2)
    (fun j => (∑ i, ‖a i j‖) ^ 2)
    (fun j => (continuous_finiteFourierSum _ _).norm.pow 2)
    (fun j t => sq_nonneg _) (fun j t =>
      pow_le_pow_left₀ (norm_nonneg _) (finiteFourierSum_bound _ _ t) 2)
    (show 1 ≤ p / 2 by linarith)
  have hb : (∑ j, b j ^ 2) = ∑ j, (∑ i, ‖a i j‖ ^ r) ^ (2 / r) := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp [b]
    rw [← Real.rpow_natCast, sequenceNorm_rpow]
    norm_num
  have hmixed := mixed_norm_comparison (fun i j => ‖a i j‖)
    (fun i j => norm_nonneg _) hr0 hr2
  have hsum' := hsum.trans ((Finset.sum_le_sum (fun j _ => hterm j)).trans_eq hb)
  have hboth := hsum'.trans hmixed
  have hI : 0 ≤ ∫ t, (∑ j, ‖F j t‖ ^ 2) ^ (p / 2) ∂ν :=
    integral_nonneg (fun t => Real.rpow_nonneg
      (Finset.sum_nonneg (fun j _ => sq_nonneg ‖F j t‖)) _)
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg hI _) hboth
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← Real.rpow_mul hI,
    ← Real.rpow_mul (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg
      (Finset.sum_nonneg (fun j _ => sq_nonneg ‖a i j‖)) _))] at hroot
  have hleft : (1 / (p / 2)) * (1 / 2) = 1 / p := by field_simp
  have hright : (2 / r) * (1 / 2) = 1 / r := by ring
  simpa only [hleft, hright, F, r] using hroot

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
