import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.NumberTheory.Ostmann.Supply.GoodSieveMultipliers

namespace OAI

/-! # Both imbalance products on the retained squarefree multipliers -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def multiplierRatioProduct (P : Finset ℕ) (κ : ℕ → ℝ) (u : ℕ) : ℝ :=
  ∏ p ∈ P, if p ∣ u then κ p else 1

theorem multiplierRatioProduct_exp_sum (P : Finset ℕ) (κ : ℕ → ℝ)
    (hκ : ∀ p ∈ P, 0 < κ p) (u : ℕ) :
    multiplierRatioProduct P κ u =
      Real.exp (∑ p ∈ P, if p ∣ u then Real.log (κ p) else 0) := by
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases h : p ∣ u
  · simp [h, Real.exp_log (hκ p hp)]
  · simp [h]

theorem multiplierRatioProduct_bounds (P : Finset ℕ) (κ : ℕ → ℝ)
    (hκ : ∀ p ∈ P, 0 < κ p) (u : ℕ) (B : ℝ)
    (hB : multiplierPrimeWeight P (fun p => |Real.log (κ p)|) u ≤ B) :
    Real.exp (-B) ≤ multiplierRatioProduct P κ u ∧
      multiplierRatioProduct P κ u ≤ Real.exp B := by
  have hsum : |∑ p ∈ P, if p ∣ u then Real.log (κ p) else 0| ≤ B := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have he : (∑ p ∈ P, |if p ∣ u then Real.log (κ p) else 0|) =
        multiplierPrimeWeight P (fun p => |Real.log (κ p)|) u := by
      unfold multiplierPrimeWeight
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p ∣ u <;> simp [hp]
    exact he.trans_le hB
  rw [multiplierRatioProduct_exp_sum P κ hκ u]
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp hsum).1,
    Real.exp_le_exp.mpr (abs_le.mp hsum).2⟩

theorem goodSieveMultipliers_ratio_products (U : ℕ) (T P : Finset ℕ) (κ : ℕ → ℝ)
    (hκ : ∀ p ∈ P, 0 < κ p) (B : ℝ) {u : ℕ}
    (hu : u ∈ goodSieveMultipliers U T P (fun p => |Real.log (κ p)|) B) :
    Real.exp (-B) ≤ multiplierRatioProduct P κ u ∧
      Real.exp (-B) ≤ multiplierRatioProduct P (fun p => (κ p)⁻¹) u := by
  have hB := (Finset.mem_filter.mp hu).2.2.2
  refine ⟨(multiplierRatioProduct_bounds P κ hκ u B hB).1, ?_⟩
  apply (multiplierRatioProduct_bounds P (fun p => (κ p)⁻¹)
    (fun p hp => inv_pos.mpr (hκ p hp)) u B ?_).1
  simpa only [Real.log_inv, abs_neg] using hB

end Ostmann

end OAI
