import OAI.NumberTheory.JointDickman.Analysis.SquarefreePerron
import OAI.NumberTheory.JointDickman.Analysis.RieszHingeBounds

namespace OAI

/-! # Positive finite-difference bounds for the squarefree Riesz primitive -/
namespace JointDickman
open Complex Finset

noncomputable def squarefreeRieszPrimitive (z x : ℝ) : ℝ :=
  x*(squarefreeRieszSum z x).re

theorem squarefreeRieszSum_re (z x : ℝ) :
    (squarefreeRieszSum z x).re =
      ∑ n ∈ range (⌊x⌋₊+1), squarefreeWeight z n*(1-(n:ℝ)/x) := by
  have h : squarefreeRieszSum z x =
      ((∑ n ∈ range (⌊x⌋₊+1), squarefreeWeight z n*(1-(n:ℝ)/x) : ℝ):ℂ) := by
    unfold squarefreeRieszSum
    push_cast
    rfl
  rw [h,ofReal_re]

theorem squarefreeRieszPrimitive_eq_sum {x : ℝ} (z : ℝ) (hx : 0 < x) :
    squarefreeRieszPrimitive z x =
      ∑ n ∈ range (⌊x⌋₊+1), squarefreeWeight z n*max (x-(n:ℝ)) 0 := by
  rw [squarefreeRieszPrimitive,squarefreeRieszSum_re,mul_sum]
  apply sum_congr rfl
  intro n hn
  have hnle : (n:ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp (by
    simpa only [mem_range,Nat.lt_succ_iff] using hn)
  rw [max_eq_left (sub_nonneg.mpr hnle)]
  field_simp

theorem squarefreeRieszPrimitive_eq_sum_to {x : ℝ} {N : ℕ} (z : ℝ) (hx : 0 < x)
    (hN : ⌊x⌋₊+1 ≤ N) :
    squarefreeRieszPrimitive z x =
      ∑ n ∈ range N, squarefreeWeight z n*max (x-(n:ℝ)) 0 := by
  rw [squarefreeRieszPrimitive_eq_sum z hx]
  apply sum_subset (range_mono hN)
  intro n _ hn
  have hnot : ¬ (n:ℝ) ≤ x := by
    intro h
    apply hn
    simpa only [mem_range,Nat.lt_succ_iff] using (Nat.le_floor_iff hx.le).mpr h
  rw [max_eq_right (by linarith : x-(n:ℝ) ≤ 0),mul_zero]

theorem squarefreeSummatory_eq_sum_range (z x : ℝ) :
    squarefreeSummatory z x = ∑ n ∈ range (⌊x⌋₊+1), squarefreeWeight z n := by
  rw [Nat.range_succ_eq_Icc_zero,←add_sum_Ioc_eq_sum_Icc (Nat.zero_le ⌊x⌋₊)]
  simp [squarefreeSummatory]

theorem squarefreeSummatory_eq_sum_to {x : ℝ} {N : ℕ} (z : ℝ) (hx : 0 ≤ x)
    (hN : ⌊x⌋₊+1 ≤ N) :
    squarefreeSummatory z x =
      ∑ n ∈ range N, if (n:ℝ) ≤ x then squarefreeWeight z n else 0 := by
  rw [squarefreeSummatory_eq_sum_range]
  calc
    _ = ∑ n ∈ range (⌊x⌋₊+1), if (n:ℝ) ≤ x then squarefreeWeight z n else 0 := by
      apply sum_congr rfl
      intro n hn
      exact (ite_eq_left ((Nat.le_floor_iff hx).mp (by
        simpa only [mem_range,Nat.lt_succ_iff] using hn))).symm
    _ = _ := by
      apply sum_subset (range_mono hN)
      intro n _ hn
      apply ite_eq_right
      intro h
      apply hn
      simpa only [mem_range,Nat.lt_succ_iff] using (Nat.le_floor_iff hx).mpr h

theorem squarefreeRieszPrimitive_difference {z x y : ℝ} (hz : 0 ≤ z)
    (hx : 0 < x) (hxy : x ≤ y) :
    (y-x)*squarefreeSummatory z x ≤ squarefreeRieszPrimitive z y-squarefreeRieszPrimitive z x ∧
    squarefreeRieszPrimitive z y-squarefreeRieszPrimitive z x ≤ (y-x)*squarefreeSummatory z y := by
  have hy : 0 < y := hx.trans_le hxy
  have hN : ⌊x⌋₊+1 ≤ ⌊y⌋₊+1 := Nat.add_le_add_right (Nat.floor_mono hxy) _
  rw [squarefreeRieszPrimitive_eq_sum_to z hx hN,
    squarefreeRieszPrimitive_eq_sum_to z hy le_rfl,
    squarefreeSummatory_eq_sum_to z hx.le hN,
    squarefreeSummatory_eq_sum_to z hy.le le_rfl]
  apply finite_riesz_difference_bounds (hxy := hxy)
  intro n _
  simp only [squarefreeWeight,ArithmeticFunction.coe_mk]
  split_ifs <;> positivity

end JointDickman

end OAI
