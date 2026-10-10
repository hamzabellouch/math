import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic

namespace OAI

/-!
# Real weights of exponent vectors

Real weights are additive on exponent vectors. Positive weights have finite sublevel sets,
and rationally independent weights distinguish exponents.
-/

open scoped BigOperators

namespace CartierSections

section Weights
variable {ι : Type*} [Fintype ι]

noncomputable def realWeight (w : ι → ℝ) (d : ι →₀ ℕ) : ℝ :=
  ∑ i, w i * (d i : ℝ)

@[simp] theorem realWeight_zero (w : ι → ℝ) : realWeight w 0 = 0 := by
  simp [realWeight]

@[simp] theorem realWeight_add (w : ι → ℝ) (d e : ι →₀ ℕ) :
    realWeight w (d + e) = realWeight w d + realWeight w e := by
  simp [realWeight, Nat.cast_add, mul_add, Finset.sum_add_distrib]

@[simp] theorem realWeight_nsmul (w : ι → ℝ) (n : ℕ) (d : ι →₀ ℕ) :
    realWeight w (n • d) = n * realWeight w d := by
  simp [realWeight, Finset.mul_sum, mul_left_comm]

theorem realWeight_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (d : ι →₀ ℕ) :
    0 ≤ realWeight w d :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Nat.cast_nonneg _)

theorem realWeight_injective {w : ι → ℝ} (hw : LinearIndependent ℚ w) :
    Function.Injective (realWeight w) := by
  intro d e h
  have he : (fun i => (d i : ℚ)) = (fun i => (e i : ℚ)) :=
    hw.fintypeLinearCombination_injective (by
      simpa [Fintype.linearCombination_apply, realWeight, Algebra.smul_def, mul_comm] using h)
  ext i
  exact_mod_cast congrFun he i

/-- Positive weights give finite sublevel sets of exponent vectors. -/
theorem finite_weight_sublevel {w : ι → ℝ} (hw : ∀ i, 0 < w i) (L : ℝ) :
    {d : ι →₀ ℕ | realWeight w d ≤ L}.Finite := by
  classical
  let b : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => ⌈L / w i⌉₊)
  apply (Set.finite_Iic b).subset
  intro d hd
  show d ≤ b
  intro i
  have hi : w i * (d i : ℝ) ≤ L :=
    le_trans (Finset.single_le_sum
      (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)) hd
  change d i ≤ ⌈L / w i⌉₊
  apply (Nat.cast_le (α := ℝ)).mp
  exact (le_div_iff₀ (hw i)).mpr (by nlinarith) |>.trans (Nat.le_ceil _)
end Weights

end CartierSections

end OAI
