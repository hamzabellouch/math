import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI

namespace Invariant233
namespace FloorCocycle

theorem floor_fract_add (x y : ℝ) :
    ⌊Int.fract x + y⌋ + ⌊x⌋ = ⌊x + y⌋ := by
  rw [Int.fract, sub_add_eq_add_sub, Int.floor_sub_intCast]
  omega

theorem floor_cocycle (u α : ℝ) (v n : ℤ) :
    ⌊u + (v : ℝ) * α⌋ + ⌊Int.fract (u + (v : ℝ) * α) + (n : ℝ) * α⌋ =
      ⌊u + ((v + n : ℤ) : ℝ) * α⌋ := by
  rw [add_comm, floor_fract_add]
  congr 1
  push_cast
  ring

theorem floor_add_eq_indicator {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u < 1) (t : ℝ) :
    ⌊u + t⌋ = ⌊t⌋ + if 1 - Int.fract t ≤ u then 1 else 0 := by
  have hsplit : ⌊u + t⌋ = ⌊u + Int.fract t⌋ + ⌊t⌋ := by
    rw [← Int.floor_add_intCast]
    congr 1
    rw [add_assoc, Int.fract_add_floor]
  rw [hsplit]
  split_ifs with h
  · have hf : ⌊u + Int.fract t⌋ = 1 := by
      apply Int.floor_eq_iff.mpr
      constructor
      · norm_num
        linarith
      · norm_num
        linarith [Int.fract_lt_one t]
    rw [hf]
    omega
  · have hf : ⌊u + Int.fract t⌋ = 0 := by
      apply Int.floor_eq_zero_iff.mpr
      constructor
      · exact add_nonneg hu₀ (Int.fract_nonneg t)
      · linarith
    rw [hf]
    omega

theorem floor_sub_eq_crossing {u w : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u < 1) (hw₀ : 0 ≤ w) (hw₁ : w < 1)
    (huw : u ≤ w) (t : ℝ) :
    ⌊w + t⌋ - ⌊u + t⌋ =
      if u < 1 - Int.fract t ∧ 1 - Int.fract t ≤ w then 1 else 0 := by
  rw [floor_add_eq_indicator hw₀ hw₁, floor_add_eq_indicator hu₀ hu₁]
  by_cases huT : 1 - Int.fract t ≤ u
  · have hwT : 1 - Int.fract t ≤ w := huT.trans huw
    simp [huT, hwT, not_lt_of_ge huT]
  · have hut : u < 1 - Int.fract t := lt_of_not_ge huT
    by_cases hwT : 1 - Int.fract t ≤ w
    · simp [huT, hwT, hut]
    · simp [huT, hwT]

theorem floor_sub_eq_one_iff {u w : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u < 1) (hw₀ : 0 ≤ w) (hw₁ : w < 1)
    (huw : u ≤ w) (t : ℝ) :
    ⌊w + t⌋ - ⌊u + t⌋ = 1 ↔
      u < 1 - Int.fract t ∧ 1 - Int.fract t ≤ w := by
  rw [floor_sub_eq_crossing hu₀ hu₁ hw₀ hw₁ huw]
  split_ifs <;> simp_all

theorem floor_sub_bounds {u w : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u < 1) (hw₀ : 0 ≤ w) (hw₁ : w < 1) (t : ℝ) :
    -1 ≤ ⌊w + t⌋ - ⌊u + t⌋ ∧ ⌊w + t⌋ - ⌊u + t⌋ ≤ 1 := by
  rw [floor_add_eq_indicator hw₀ hw₁, floor_add_eq_indicator hu₀ hu₁]
  split_ifs <;> omega

theorem no_crossing_of_fract_eq_zero {u w t : ℝ} (hw₁ : w < 1)
    (ht : Int.fract t = 0) :
    ¬ (u < 1 - Int.fract t ∧ 1 - Int.fract t ≤ w) := by
  rw [ht]
  simp only [sub_zero]
  intro h
  linarith [h.2]

theorem exp_ratio_eq_crossing {u w : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u < 1) (hw₀ : 0 ≤ w) (hw₁ : w < 1)
    (huw : u ≤ w) (c t : ℝ) :
    Real.exp (-c * (⌊w + t⌋ : ℝ)) / Real.exp (-c * (⌊u + t⌋ : ℝ)) =
      if u < 1 - Int.fract t ∧ 1 - Int.fract t ≤ w then Real.exp (-c) else 1 := by
  rw [← Real.exp_sub]
  have he : -c * (⌊w + t⌋ : ℝ) - -c * (⌊u + t⌋ : ℝ) =
      -c * ((⌊w + t⌋ - ⌊u + t⌋ : ℤ) : ℝ) := by
    push_cast
    ring
  rw [he, floor_sub_eq_crossing hu₀ hu₁ hw₀ hw₁ huw]
  split_ifs <;> simp

theorem exp_ratio_le_one {u w c : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u < 1) (hw₀ : 0 ≤ w) (hw₁ : w < 1)
    (huw : u ≤ w) (hc : 0 ≤ c) (t : ℝ) :
    Real.exp (-c * (⌊w + t⌋ : ℝ)) / Real.exp (-c * (⌊u + t⌋ : ℝ)) ≤ 1 := by
  rw [exp_ratio_eq_crossing hu₀ hu₁ hw₀ hw₁ huw]
  split_ifs
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hc)
  · exact le_rfl

theorem exp_ratio_bounds {u w c : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u < 1) (hw₀ : 0 ≤ w) (hw₁ : w < 1)
    (hc : 0 ≤ c) (t : ℝ) :
    Real.exp (-c) ≤ Real.exp (-c * (⌊w + t⌋ : ℝ)) /
        Real.exp (-c * (⌊u + t⌋ : ℝ)) ∧
      Real.exp (-c * (⌊w + t⌋ : ℝ)) /
        Real.exp (-c * (⌊u + t⌋ : ℝ)) ≤ Real.exp c := by
  obtain ⟨hlo, hhi⟩ := floor_sub_bounds hu₀ hu₁ hw₀ hw₁ t
  have hlo' : (-1 : ℝ) ≤ (⌊w + t⌋ : ℝ) - (⌊u + t⌋ : ℝ) := by
    exact_mod_cast hlo
  have hhi' : (⌊w + t⌋ : ℝ) - (⌊u + t⌋ : ℝ) ≤ 1 := by
    exact_mod_cast hhi
  rw [← Real.exp_sub]
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith
  · apply Real.exp_le_exp.mpr
    nlinarith

end FloorCocycle
end Invariant233

end OAI
