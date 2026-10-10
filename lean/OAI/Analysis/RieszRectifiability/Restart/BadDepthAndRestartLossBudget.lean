import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.RestartLossBudget
import OAI.Analysis.RieszRectifiability.Restart.BadBetaStopping

namespace OAI

/-!
# Combined bad-depth and restart loss budgets

For a fixed AD-regular measure with a bounded Riesz transform, a multiplicity
threshold makes the mass at large bad-beta depth arbitrarily small. Splitting
the prescribed tolerance in half combines this estimate with the summed losses
over restart cells, uniformly over admissible root cells.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem original_AD_Riesz_bad_depth_loss_budget {p d : ℕ} (hnd : p + 1 ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular (p + 1) μ)
    (hRiesz : RieszL2Bounded (p + 1) μ) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      μ {x | (N : ℝ≥0∞) ≤ badBetaMultiplicity (p + 1) μ R hR k z H ε x} ≤
        ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨K, hK, hstop⟩ := original_AD_Riesz_bad_beta_stopping hnd μ hAD hRiesz H ε hH hε
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (K / ζ))
  have hN1 : 1 ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hNratio : K / ζ ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by exact_mod_cast lt_of_lt_of_le zero_lt_one hN1
  have hNrpos : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hratio : K / (N : ℝ) ≤ ζ := by
    apply (div_le_iff₀ hNrpos).mpr
    have h := (div_le_iff₀ hζ).mp hNratio
    nlinarith
  have hcoef : ENNReal.ofReal K / (N : ℝ≥0∞) ≤ ENNReal.ofReal ζ := by
    have h := ENNReal.ofReal_le_ofReal hratio
    simpa only [ENNReal.ofReal_div_of_pos hNrpos, ENNReal.ofReal_natCast] using! h
  refine ⟨N, hNpos, ?_⟩
  intro R hR k z hcore
  have ht := (hstop R hR k z hcore).1 (N : ℝ≥0∞) (by exact_mod_cast hNpos.ne') (by simp)
  calc
    _ ≤ (ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z)) / (N : ℝ≥0∞) := ht
    _ = (ENNReal.ofReal K / (N : ℝ≥0∞)) * μ (cleanSupportCell μ R hR k z) := by
      simp only [div_eq_mul_inv, mul_right_comm]
    _ ≤ _ := mul_le_mul_left hcoef _

theorem original_AD_Riesz_combined_restart_loss_budget {p d : ℕ} (hnd : p + 1 ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular (p + 1) μ)
    (hRiesz : RieszL2Bounded (p + 1) μ) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∀ loss : {i : SupportCellDescendant μ R hR k z // cellRestartsAfter
        (fun q => ε ≤ bilateralBeta (p + 1) μ q.center (H * q.radius)) i} → ℝ≥0∞,
        (∀ i, loss i ≤ ENNReal.ofReal δ * μ i.val.cell) →
        (∑' i, loss i) +
          μ {x | (N : ℝ≥0∞) ≤ badBetaMultiplicity (p + 1) μ R hR k z H ε x} ≤
          ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨δ, hδ, hregions⟩ := original_AD_Riesz_restart_loss_budget hnd μ hAD hRiesz H ε hH hε
    (ζ / 2) (half_pos hζ)
  obtain ⟨N, hN, hdepth⟩ := original_AD_Riesz_bad_depth_loss_budget hnd μ hAD hRiesz H ε hH hε
    (ζ / 2) (half_pos hζ)
  refine ⟨δ, hδ, N, hN, ?_⟩
  intro R hR k z hcore loss hloss
  have h := add_le_add (hregions R hR k z hcore loss hloss) (hdepth R hR k z hcore)
  have heq : ENNReal.ofReal (ζ / 2) + ENNReal.ofReal (ζ / 2) = ENNReal.ofReal ζ := by
    rw [← ENNReal.ofReal_add (half_pos hζ).le (half_pos hζ).le, add_halves]
  simpa only [← add_mul, heq] using! h

end

end RieszRectifiability

end OAI
