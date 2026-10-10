import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateNormalization

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate HigherBiasSourceWord Preliminaries
attribute [local instance] Classical.propDecidable

theorem actualCopiedNormalization_le_power {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) {ρ c₀ c β L : ℝ}
    (hρ : 0 < ρ) (hc₀ : 0 < c₀) (hc : 0 < c) (hL : 0 < L) (hβ : 0 ≤ β+1)
    (hbulk : ρ*L ≤ primeShellMass bulk) (htop : c₀ ≤ primeShellMass top)
    (hcell : ∀ a, c/Real.exp (β*L) ≤ primeShellMass (configurationCells E cfg a))
    (hLc : -Real.log c ≤ L)
    (hbudget : 2*(β+1)*(configCellCount cfg:ℝ)*L ≤ 2*(m:ℝ)) :
    copiedNormalization (actualCopiedShells cfg m j bulk top E) ≤
      L ^ (-((2^j*m:ℕ):ℝ)) * Real.exp
        ((|Real.log ρ|+2)*((2^j*m:ℕ):ℝ)+(2^j:ℕ)*|Real.log c₀|) := by
  classical
  have hh := actualCopiedNormalization_le_exp cfg m j bulk top E
    (mul_pos hρ hL) hc₀ (mul_nonneg hβ hL.le) hbulk htop
    (fun a => PivotProductNormalization.primeShellMass_exp_lower
      (configurationCells E cfg a) hc (Real.exp_pos _) (hcell a) le_rfl hLc)
  apply hh.trans
  have hρ' := mul_le_mul_of_nonneg_left (neg_le_abs (Real.log ρ))
    (show 0 ≤ (2^j:ℕ)*(m:ℝ) by positivity)
  have hc₀' := mul_le_mul_of_nonneg_left (neg_le_abs (Real.log c₀))
    (show 0 ≤ ((2^j:ℕ):ℝ) by positivity)
  have hb := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ ((2^j:ℕ):ℝ) by positivity)
  calc
    _ ≤ Real.exp (-((2^j*m:ℕ):ℝ)*Real.log L +
        ((|Real.log ρ|+2)*((2^j*m:ℕ):ℝ)+(2^j:ℕ)*|Real.log c₀|)) := by
      apply Real.exp_le_exp.mpr
      rw [Real.log_mul hρ.ne' hL.ne']
      push_cast at hρ' hc₀' hb ⊢
      nlinarith
    _ = _ := by
      rw [Real.rpow_def_of_pos hL,← Real.exp_add]
      congr 1
      ring

end Ostmann.Characters.DiagonalEstimate

end

end OAI
