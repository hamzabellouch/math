import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6

def average {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i

theorem average_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → ℝ) : average (f ∘ e) = average f := by
  simp only [average, Fintype.card_congr e, Function.comp_apply, e.sum_comp]

theorem average_eq_zero_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (h : ∀ i, 0 ≤ f i) : average f = 0 ↔ ∀ i, f i = 0 := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card ι))
  simp only [average, mul_eq_zero, inv_eq_zero, hc, false_or]
  simpa using Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => h i)

theorem average_nonneg {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (h : ∀ i, 0 ≤ f i) : 0 ≤ average f := by
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => h i))

theorem average_le_one {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (h : ∀ i, f i ≤ 1) : average f ≤ 1 := by
  classical
  by_cases hc : Fintype.card ι = 0
  · simp [average, hc]
  · have hs : ∑ i, f i ≤ (Fintype.card ι : ℝ) := by
      calc
        _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => h i)
        _ = _ := by simp
    have hp : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Nat.pos_of_ne_zero hc
    calc
      average f ≤ (Fintype.card ι : ℝ)⁻¹ * Fintype.card ι :=
        mul_le_mul_of_nonneg_left hs (le_of_lt (inv_pos.mpr hp))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hp)

theorem abs_average_le_one {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (h : ∀ i, |f i| ≤ 1) : |average f| ≤ 1 := by
  calc
    |average f| ≤ average (fun i => |f i|) := by
      simp only [average, abs_mul, abs_inv]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Fintype.card ι)]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
        (by positivity)
    _ ≤ 1 := average_le_one _ h

end MUB6

end

end OAI
