import OAI.Combinatorics.YoungDiagram.Capacity
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs

namespace OAI

/-! The opposite-prefix capacity bound with real upper bounds and an integer floor. -/

namespace ArithmeticTensorSquares.Capacity

theorem capacity_rectangle_real (μ : YoungDiagram) (i j : Nat) (U V : ℝ)
    (hμ : 0 < μ.card) (hi : 0 < i) (hj : 0 < j)
    (hU : (colPrefix μ i : ℝ) ≤ U) (hV : (rowPrefix μ j : ℝ) ≤ V) :
    (μ.card : ℝ) ≤ max (U + V - 1)
      (Int.floor (U * V / ((i * j : Nat) : ℝ)) : ℝ) := by
  rcases native_rectangle_sharp μ i j hμ hi hj with hsum | hprod
  · have hsumNat : μ.card + 1 ≤ colPrefix μ i + rowPrefix μ j := by omega
    have hsumReal : (μ.card : ℝ) + 1 ≤
        (colPrefix μ i : ℝ) + (rowPrefix μ j : ℝ) := by
      exact_mod_cast hsumNat
    have hbound : (μ.card : ℝ) ≤ U + V - 1 := by linarith
    exact le_trans hbound (le_max_left _ _)
  · have hU_nonneg : 0 ≤ U := le_trans (Nat.cast_nonneg _) hU
    have hrow_nonneg : (0 : ℝ) ≤ (rowPrefix μ j : ℝ) := Nat.cast_nonneg _
    have hproduct : (colPrefix μ i : ℝ) * (rowPrefix μ j : ℝ) ≤ U * V :=
      mul_le_mul hU hV hrow_nonneg hU_nonneg
    have hprodReal : ((i * j : Nat) : ℝ) * (μ.card : ℝ) ≤
        (colPrefix μ i : ℝ) * (rowPrefix μ j : ℝ) := by
      exact_mod_cast hprod
    have hden : (0 : ℝ) < ((i * j : Nat) : ℝ) := by
      exact_mod_cast Nat.mul_pos hi hj
    have hquotient : (μ.card : ℝ) ≤ U * V / ((i * j : Nat) : ℝ) :=
      (le_div_iff₀ hden).mpr (by
        simpa only [mul_comm] using le_trans hprodReal hproduct)
    have hfloor : (μ.card : ℤ) ≤ Int.floor (U * V / ((i * j : Nat) : ℝ)) :=
      Int.le_floor.mpr (by simpa only [Int.cast_natCast] using hquotient)
    have hbound : (μ.card : ℝ) ≤
        (Int.floor (U * V / ((i * j : Nat) : ℝ)) : ℝ) := by
      exact_mod_cast hfloor
    exact le_trans hbound (le_max_right _ _)

end ArithmeticTensorSquares.Capacity

end OAI
