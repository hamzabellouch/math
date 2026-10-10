import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceNormalizedData
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedNumericInputsGrowth

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap
namespace Ostmann.Characters.TemplateOneSidedCancellation
open TemplateOneSidedNumericInputs Arithmetic

lemma historyPolynomialCost_mono_coefficient {C D : ℝ} (h : C ≤ D) (z L : ℝ) (n : ℕ) :
    historyPolynomialCost C z n L ≤ historyPolynomialCost D z n L :=
  mul_le_mul_of_nonneg_right h (by positivity)

lemma linear_le_exp_quartic_cost (A z L : ℝ) (hA : 0 ≤ A) :
    A * (1 + (⌊z * L⌋₊ : ℝ)) ≤ Real.exp (historyPolynomialCost (A + 1) z 4 L) := by
  let m : ℝ := 1 + (⌊z * L⌋₊ : ℝ)
  have hm : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α:=ℝ) ⌊z*L⌋₊]
  have hh := coefficient_pow_exp_le m A 0 0 1 hm hA (by simp)
  simp only [pow_one, Real.exp_zero, mul_one, Nat.cast_one, add_zero] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  change (A + 1) * m ≤ (A + 1) * m^4
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  simpa only [pow_one] using pow_le_pow_right₀ hm (show 1 ≤ 4 by omega)

lemma constant_mul_exp_quartic_cost (A C z L : ℝ) (hA : 0 ≤ A) :
    A * Real.exp (historyPolynomialCost C z 4 L) ≤
      Real.exp (historyPolynomialCost (A + C) z 4 L) := by
  let m : ℝ := (1 + (⌊z * L⌋₊ : ℝ))^4
  have hm : 1 ≤ m := one_le_pow₀ (by have h := Nat.cast_nonneg (α:=ℝ) ⌊z*L⌋₊; linarith)
  have hh := coefficient_pow_exp_le m A (C*m) C 0 hm hA le_rfl
  simpa only [pow_zero, mul_one, Nat.cast_zero, add_zero, m, historyPolynomialCost] using hh

lemma coarseProfile_width_le (D : ℕ) {H Δ W : ℝ} (hH : 0 ≤ H) :
    (-Δ + W) - coarseLower D H Δ W ≤ (D : ℝ)*H + |Δ| + |W| := by
  have hD : 0 ≤ (D : ℝ)*H := mul_nonneg (Nat.cast_nonneg _) hH
  unfold coarseLower
  by_cases h : -(D : ℝ)*H ≤ -Δ + W
  · rw [min_eq_left h]
    linarith [neg_le_abs Δ, le_abs_self W]
  · rw [min_eq_right (le_of_not_ge h)]
    linarith [abs_nonneg Δ, abs_nonneg W]

lemma normalizedProfile_width_eq (j D : ℕ) (H Δ Wl Wc : ℝ) :
    (3 + ∑ i : Unit ⊕ (Fin (2^j) ⊕ Fin (2^j)),
      (Sum.elim (fun _ : Unit => Wc) (fun _ : Fin (2^j) ⊕ Fin (2^j) => -Δ + Wl) i -
        Sum.elim (fun _ : Unit => -Wc)
          (fun _ : Fin (2^j) ⊕ Fin (2^j) => coarseLower D H Δ Wl) i)) =
      3 + 2*Wc + (2*(2:ℝ)^j)*((-Δ + Wl) - coarseLower D H Δ Wl) := by
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, 
    Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_unique, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  ring

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
