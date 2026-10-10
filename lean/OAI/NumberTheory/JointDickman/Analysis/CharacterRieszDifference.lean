import OAI.NumberTheory.JointDickman.Analysis.ComplexRieszDifference
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeCharacterPerron
import OAI.NumberTheory.JointDickman.Analysis.CharacterPerronIntegrable

namespace OAI

/-! # Finite differences of the actual character Riesz primitive -/
namespace JointDickman
open Complex Finset

noncomputable def squarefreeCharacterPrimitive {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z x : ℝ) : ℂ := (x:ℂ)*squarefreeCharacterRieszSum χ z x

theorem squarefreeCharacterPrimitive_eq_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {x : ℝ} (hx : 0 < x) :
    squarefreeCharacterPrimitive χ z x =
      ∑ n ∈ range (⌊x⌋₊+1), (squarefreeWeight z n:ℂ)*χ (n:ZMod q)*(max (x-(n:ℝ)) 0:ℝ) := by
  rw [squarefreeCharacterPrimitive, squarefreeCharacterRieszSum, mul_sum]
  apply sum_congr rfl
  intro n hn
  have hnle : (n:ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp (by
    simpa only [mem_range, Nat.lt_succ_iff] using hn)
  rw [max_eq_left (sub_nonneg.mpr hnle)]
  push_cast
  field_simp [show (x:ℂ) ≠ 0 by exact_mod_cast hx.ne']

theorem squarefreeCharacterPrimitive_eq_sum_to {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {x : ℝ} {N : ℕ} (hx : 0 < x) (hN : ⌊x⌋₊+1 ≤ N) :
    squarefreeCharacterPrimitive χ z x =
      ∑ n ∈ range N, (squarefreeWeight z n:ℂ)*χ (n:ZMod q)*(max (x-(n:ℝ)) 0:ℝ) := by
  rw [squarefreeCharacterPrimitive_eq_sum χ z hx]
  apply sum_subset (range_mono hN)
  intro n _ hn
  have hnot : ¬(n:ℝ) ≤ x := by
    intro h
    apply hn
    simpa only [mem_range, Nat.lt_succ_iff] using (Nat.le_floor_iff hx.le).mpr h
  rw [max_eq_right (by linarith : x-(n:ℝ) ≤ 0)]
  simp

theorem squarefreeCharacterSum_eq_sum_range {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z x : ℝ) :
    squarefreeCharacterSum χ z x = ∑ n ∈ range (⌊x⌋₊+1),
      (squarefreeWeight z n:ℂ)*χ (n:ZMod q) := by
  rw [Nat.range_succ_eq_Icc_zero, ←add_sum_Ioc_eq_sum_Icc (Nat.zero_le ⌊x⌋₊)]
  simp [squarefreeCharacterSum]

theorem squarefreeCharacterSum_eq_sum_to {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {x : ℝ} {N : ℕ} (hx : 0 ≤ x) (hN : ⌊x⌋₊+1 ≤ N) :
    squarefreeCharacterSum χ z x =
      ∑ n ∈ range N, if (n:ℝ) ≤ x then (squarefreeWeight z n:ℂ)*χ (n:ZMod q) else 0 := by
  rw [squarefreeCharacterSum_eq_sum_range]
  calc
    _ = ∑ n ∈ range (⌊x⌋₊+1), if (n:ℝ) ≤ x then
        (squarefreeWeight z n:ℂ)*χ (n:ZMod q) else 0 := by
      apply sum_congr rfl
      intro n hn
      exact (ite_eq_left ((Nat.le_floor_iff hx).mp (by
        simpa only [mem_range, Nat.lt_succ_iff] using hn))).symm
    _ = _ := by
      apply sum_subset (range_mono hN)
      intro n _ hn
      apply ite_eq_right
      intro h
      apply hn
      simpa only [mem_range, Nat.lt_succ_iff] using (Nat.le_floor_iff hx).mpr h

theorem squarefreeCharacterPrimitive_difference {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z x y : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hx : 0 < x) (hxy : x ≤ y) :
    ‖squarefreeCharacterPrimitive χ z y-squarefreeCharacterPrimitive χ z x-
      ((y-x):ℂ)*squarefreeCharacterSum χ z x‖ ≤ (y-x)*(y-x+1) := by
  have hy : 0 < y := hx.trans_le hxy
  have hN : ⌊x⌋₊+1 ≤ ⌊y⌋₊+1 := Nat.add_le_add_right (Nat.floor_mono hxy) _
  rw [squarefreeCharacterPrimitive_eq_sum_to χ z hy le_rfl,
    squarefreeCharacterPrimitive_eq_sum_to χ z hx hN,
    squarefreeCharacterSum_eq_sum_to χ z hx.le hN]
  have hb := finite_complex_riesz_difference_bound (range (⌊y⌋₊+1))
    (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (fun n => (n:ℝ))
    (fun n _ => squarefreeCharacterWeight_norm_le_one χ hz hz1 n) hxy
  have he : (range (⌊y⌋₊+1)).filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) ≤ y) = Ioc ⌊x⌋₊ ⌊y⌋₊ := by
    ext n
    simp only [mem_filter, mem_range, Nat.lt_succ_iff, mem_Ioc,
      Nat.le_floor_iff hy.le, Nat.floor_lt hx.le]
    tauto
  rw [he, Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono hxy)] at hb
  have hcount : (⌊y⌋₊:ℝ)-(⌊x⌋₊:ℝ) ≤ y-x+1 := by
    have hl := Nat.floor_le hy.le
    have hu := Nat.lt_floor_add_one x
    linarith
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hcount (sub_nonneg.mpr hxy)])

end JointDickman

end OAI
