import Mathlib.Data.Int.Interval
import OAI.NumberTheory.Jacobsthal.Harmonic.CharacterChord

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaFourier

noncomputable def lowerCut (x : ℝ) (closed : Bool) : ℤ :=
  if closed then ⌈x⌉ else ⌊x⌋+1

noncomputable def upperCut (x : ℝ) (closed : Bool) : ℤ := lowerCut x (!closed)

theorem lowerCut_le_iff (x : ℝ) (closed : Bool) (j : ℤ) :
    lowerCut x closed ≤ j ↔ if closed then x ≤ (j : ℝ) else x < (j : ℝ) := by
  cases closed <;> simp [lowerCut, Int.floor_lt, Int.ceil_le]

theorem lt_upperCut_iff (x : ℝ) (closed : Bool) (j : ℤ) :
    j < upperCut x closed ↔ if closed then (j : ℝ) ≤ x else (j : ℝ) < x := by
  cases closed <;> simp [upperCut, lowerCut, Int.le_floor, Int.lt_ceil]

theorem lowerCut_bounds (x : ℝ) (closed : Bool) :
    x ≤ (lowerCut x closed : ℝ) ∧ (lowerCut x closed : ℝ) ≤ x+1 := by
  have hf := Int.floor_le x
  have hf' := Int.lt_floor_add_one x
  have hc := Int.le_ceil x
  have hc' := Int.ceil_lt_add_one x
  cases closed <;> simp only [lowerCut, Bool.false_eq_true, ite_false, ite_true, Int.cast_add,
    Int.cast_one] <;> constructor <;> linarith

theorem upperCut_bounds (x : ℝ) (closed : Bool) :
    x ≤ (upperCut x closed : ℝ) ∧ (upperCut x closed : ℝ) ≤ x+1 :=
  lowerCut_bounds x (!closed)

theorem cut_count_error (x y : ℝ) (hxy : x ≤ y) (lc rc : Bool) :
    |(((upperCut y rc-lowerCut x lc).toNat : ℕ) : ℝ) - (y-x)| ≤ 1 := by
  obtain ⟨hL, hL'⟩ := lowerCut_bounds x lc
  obtain ⟨hU, hU'⟩ := upperCut_bounds y rc
  by_cases hpos : 0 ≤ upperCut y rc-lowerCut x lc
  · have hc : (((upperCut y rc-lowerCut x lc).toNat : ℕ) : ℝ) =
        (upperCut y rc : ℝ)-(lowerCut x lc : ℝ) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hpos)
      push_cast at h
      exact h
    rw [hc, abs_le]
    constructor <;> linarith
  · have hc : (upperCut y rc-lowerCut x lc).toNat = 0 := Int.toNat_of_nonpos (by omega)
    have hUL : (upperCut y rc : ℝ) ≤ (lowerCut x lc : ℝ) := by exact_mod_cast (by omega : upperCut y rc ≤ lowerCut x lc)
    rw [hc]
    norm_num only [Nat.cast_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    linarith

end ErdosHyperbolaFourier

end

end Erdos970

end OAI
