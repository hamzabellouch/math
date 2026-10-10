import Mathlib.Analysis.Complex.Basic
import OAI.NumberTheory.Ostmann.Construction.FiniteCellMeans

namespace OAI

/-! # Complex averages on the actual prime cells -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def complexCellMean (P : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ)
    (F : ℕ → ℂ) (h : ℕ) : ℂ :=
  (finiteCellMass P label μ h : ℂ)⁻¹ *
    ∑ p ∈ P.filter (fun p => label p = h), (μ p : ℂ) * F p

theorem complexCellMean_re (P : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ)
    (F : ℕ → ℂ) (h : ℕ) :
    (complexCellMean P label μ F h).re = finiteCellMean P label μ (fun p => (F p).re) h := by
  simp [complexCellMean, finiteCellMean, ← Complex.ofReal_inv, Complex.mul_re, Complex.re_sum]

theorem complexCellMean_norm_le_one (P : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ)
    (F : ℕ → ℂ) (hμ : ∀ p ∈ P, 0 ≤ μ p) (hF : ∀ p ∈ P, ‖F p‖ ≤ 1) (h : ℕ) :
    ‖complexCellMean P label μ F h‖ ≤ 1 := by
  have hm := finiteCellMass_nonneg P label μ hμ h
  by_cases hz : finiteCellMass P label μ h = 0
  · simp [complexCellMean, hz]
  · have hsum : ‖∑ p ∈ P.filter (fun p => label p = h), (μ p : ℂ) * F p‖ ≤
        finiteCellMass P label μ h := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p hp
      have hpP := (Finset.mem_filter.mp hp).1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ p hpP)]
      exact mul_le_of_le_one_right (hμ p hpP) (hF p hpP)
    rw [complexCellMean, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm]
    calc
      _ ≤ (finiteCellMass P label μ h)⁻¹ * finiteCellMass P label μ h :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hm)
      _ = 1 := inv_mul_cancel₀ hz

end Ostmann

end OAI
