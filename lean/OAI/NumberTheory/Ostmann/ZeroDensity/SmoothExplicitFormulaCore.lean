import Mathlib.Topology.Algebra.InfiniteSum.Real
import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedSmoothExplicitFormula
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothMellinBounds
import OAI.NumberTheory.Ostmann.ZeroDensity.HighZeroTailBound

namespace OAI

/-! # Removing the elementary fields of the smooth explicit-formula input

The analytic input is only the zero count and fixed-test explicit formula.
The Mellin decay and absolute summability are derived for the actual test.
-/

namespace Ostmann

open Finset
open scoped Classical BigOperators

/-- The fixed-test explicit formula. -/
structure SmoothExplicitFormulaCore (Z : ∀ χ, ComplexZeroEnumeration χ) where
  errorConstant : ℝ
  errorConstant_pos : 0 < errorConstant
  zeroCountConstant : ℝ
  zeroCountConstant_pos : 0 < zeroCountConstant
  zero_count : ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 0 ≤ T →
    ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ((Z χ).count 0 T : ℝ)) ≤
        zeroCountConstant * (Q : ℝ) ^ 2 * (T + 1) * Real.log ((Q : ℝ) * (T + 2))
  explicit_formula : ∀ χ : PrimitiveComplexCharacter, ∀ X : ℝ, 2 ≤ X →
    ‖smoothMangoldtMean χ.modulus χ.character X +
      (∑' i, smoothZeroTerm Z χ X i) + smoothTrivialZeroTerm χ‖ ≤
        errorConstant / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ))

theorem SmoothExplicitFormulaCore.finite_height_count {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : SmoothExplicitFormulaCore Z) (χ : PrimitiveComplexCharacter) (S : Finset ℕ)
    (T : ℝ) (hT : 0 ≤ T) :
    (((S.filter fun i => |((Z χ).zeros i).im| ≤ T).card : ℝ)) ≤
      (P.zeroCountConstant * (χ.modulus : ℝ) ^ 2) * (T + 1) *
        Real.log ((χ.modulus : ℝ) * (T + 2)) := by
  have hsub : (S.filter fun i => |((Z χ).zeros i).im| ≤ T) ⊆ (Z χ).heightIndices T := by
    intro i hi
    exact ((Z χ).mem_heightIndices T i).mpr (mem_filter.mp hi).2
  have hcard : ((Z χ).heightIndices T).card = (Z χ).count 0 T := by
    unfold ComplexZeroEnumeration.count
    rw [filter_eq_self.mpr (fun i _ => ((Z χ).in_strip i).1.le)]
  have h := P.zero_count χ.modulus (Nat.succ_le_iff.mpr χ.positive) T hT {χ} (by simp)
  simp only [sum_singleton] at h
  calc
    _ ≤ (((Z χ).heightIndices T).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ = ((Z χ).count 0 T : ℝ) := by rw [hcard]
    _ ≤ _ := h

theorem smoothZeroTerm_bound_of_mellin {Z : ∀ χ, ComplexZeroEnumeration χ}
    (C : ℝ)
    (hM : ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖primeMeanMellin s‖ ≤ C * Real.exp (-8 * Real.log (1 + |s.im|)))
    (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 1 ≤ X) (i : ℕ) :
    ‖smoothZeroTerm Z χ X i‖ ≤
      (X * C) * Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|)) := by
  have hs := (Z χ).in_strip i
  have hm := hM ((Z χ).zeros i) (by linarith) (by linarith)
  have hX0 : 0 < X := by linarith
  have he : Real.exp (((Z χ).zeros i).re * Real.log X) ≤ X := by
    calc
      _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.2.le (Real.log_nonneg hX))
      _ = X := Real.exp_log hX0
  rw [smoothZeroTerm, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc
    _ ≤ X * (C * Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|))) :=
      mul_le_mul he hm (norm_nonneg _) hX0.le
    _ = _ := by ring

theorem SmoothExplicitFormulaCore.absolute_summability {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : SmoothExplicitFormulaCore Z) (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 2 ≤ X) : Summable (fun i => ‖smoothZeroTerm Z χ X i‖) := by
  obtain ⟨C, hC, hM⟩ := primeMeanMellin_decay
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  apply summable_of_sum_le (fun i => norm_nonneg _)
    (c := (X * C) * (2 * (2 * (P.zeroCountConstant * (χ.modulus : ℝ) ^ 2) *
      (Real.log χ.modulus + 3)) ^ 2))
  intro S
  have hh := finite_high_zero_tail_bound S (fun i => |((Z χ).zeros i).im|)
    (χ.modulus : ℝ) (P.zeroCountConstant * (χ.modulus : ℝ) ^ 2) 0 hq
    (mul_nonneg P.zeroCountConstant_pos.le (sq_nonneg _)) le_rfl
    (fun _ _ => abs_nonneg _) (P.finite_height_count χ S)
  simp only [add_zero, Real.log_one, mul_zero, Real.exp_zero, mul_one] at hh
  calc
    _ ≤ ∑ i ∈ S, (X * C) * Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|)) :=
      sum_le_sum (fun i _ => smoothZeroTerm_bound_of_mellin C hM χ X (by linarith) i)
    _ = (X * C) * ∑ i ∈ S, Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|)) :=
      (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

noncomputable def SmoothExplicitFormulaCore.toPublished {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : SmoothExplicitFormulaCore Z) : PublishedSmoothExplicitFormula Z where
  errorConstant := P.errorConstant
  errorConstant_pos := P.errorConstant_pos
  mellinConstant := Classical.choose primeMeanMellin_decay
  mellinConstant_pos := (Classical.choose_spec primeMeanMellin_decay).1
  mellin_decay := (Classical.choose_spec primeMeanMellin_decay).2
  zeroCountConstant := P.zeroCountConstant
  zeroCountConstant_pos := P.zeroCountConstant_pos
  zero_count := P.zero_count
  absolute_summability := P.absolute_summability
  explicit_formula := P.explicit_formula

end Ostmann

end OAI
