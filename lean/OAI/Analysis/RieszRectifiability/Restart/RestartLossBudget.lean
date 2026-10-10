import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.BadBetaRestartPacking

namespace OAI

/-!
# Summing relative losses over restarts

A packing bound for restart-cell masses turns a uniform relative loss bound into a total
budget. Choosing the relative tolerance as the requested budget divided by the positive
packing constant yields the original AD/Riesz restart estimate.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem relative_losses_sum_le_packed_mass {ι : Type*}
    (mass loss : ι → ℝ≥0∞) (δ K T : ℝ≥0∞)
    (hloss : ∀ i, loss i ≤ δ * mass i) (hpack : ∑' i, mass i ≤ K * T) :
    (∑' i, loss i) ≤ (δ * K) * T := by
  calc
    _ ≤ ∑' i, δ * mass i := ENNReal.tsum_le_tsum hloss
    _ = δ * ∑' i, mass i := ENNReal.tsum_mul_left
    _ ≤ δ * (K * T) := mul_le_mul_right hpack δ
    _ = _ := (mul_assoc _ _ _).symm

theorem original_AD_Riesz_restart_loss_budget {p d : ℕ} (hnd : p + 1 ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular (p + 1) μ)
    (hRiesz : RieszL2Bounded (p + 1) μ) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∀ loss : {i : SupportCellDescendant μ R hR k z // cellRestartsAfter
        (fun q => ε ≤ bilateralBeta (p + 1) μ q.center (H * q.radius)) i} → ℝ≥0∞,
        (∀ i, loss i ≤ ENNReal.ofReal δ * μ i.val.cell) →
        (∑' i, loss i) ≤ ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨K, hK, hpack⟩ := original_AD_Riesz_bad_beta_restart_mass hnd μ hAD hRiesz H ε hH hε
  refine ⟨ζ / K, div_pos hζ hK, ?_⟩
  intro R hR k z hcore loss hloss
  have h := relative_losses_sum_le_packed_mass (fun i => μ i.val.cell) loss
    (ENNReal.ofReal (ζ / K)) (ENNReal.ofReal K) (μ (cleanSupportCell μ R hR k z))
    hloss (hpack R hR k z hcore)
  have heq : ENNReal.ofReal (ζ / K) * ENNReal.ofReal K = ENNReal.ofReal ζ := by
    rw [← ENNReal.ofReal_mul (div_nonneg hζ.le hK.le), div_mul_cancel₀ ζ hK.ne']
  rwa [heq] at h

end

end RieszRectifiability

end OAI
