import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTAmplificationPower
import Mathlib.Algebra.Order.Field.GeomSum

namespace OAI

/-! The exponential sum over the first MRT prime band. Its constant is
independent of the number of coarse bins. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_exp_geometric_sum {β H : ℝ} (hβ : 0 < β) (hH : 0 < H) (m n : ℕ) :
    (∑ k ∈ Icc m n, Real.exp (-β * (k : ℝ) / H)) ≤
      Real.exp (-β * (m : ℝ) / H) / (1 - Real.exp (-β / H)) := by
  let q := Real.exp (-β / H)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by linarith : -β < 0) hH
  have he (k : ℕ) : Real.exp (-β * (k : ℝ) / H) = q ^ k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hs : Icc m n = Ico m (n + 1) := by
    ext k
    simp only [mem_Icc, mem_Ico]
    omega
  simp_rw [he]
  rw [hs]
  exact geom_sum_Ico_le_of_lt_one hq0 hq1

lemma mrt_geometric_denominator_bound {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    1 / (1 - Real.exp (-x)) ≤ 2 / x := by
  have hex : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hinv : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hex
  have hgap : x / 2 ≤ 1 - Real.exp (-x) := by
    calc
      _ ≤ x / (1 + x) := div_le_div_of_nonneg_left hx.le (by positivity) (by linarith)
      _ = 1 - 1 / (1 + x) := by
        field_simp [show (1 : ℝ) + x ≠ 0 by positivity]
        ring
      _ ≤ _ := sub_le_sub_left hinv 1
  calc
    _ ≤ 1 / (x / 2) := one_div_le_one_div_of_le (by positivity) hgap
    _ = _ := by ring

theorem mrt_first_band_exponential_sum {β H P : ℝ}
    (hβ : 0 < β) (hH : 0 < H) (hβH : β ≤ H) (hP : 1 ≤ P) (n : ℕ) :
    (∑ k ∈ Icc ⌊H * Real.log P⌋₊ n, Real.exp (-β * (k : ℝ) / H)) ≤
      (2 * Real.exp 1 * H / β) * P ^ (-β) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  let m : ℕ := ⌊H * Real.log P⌋₊
  have hfloor : H * Real.log P < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hbase : -β * (m : ℝ) / H ≤ -β * Real.log P + β / H := by
    apply (div_le_iff₀ hH).mpr
    have hh := mul_le_mul_of_nonneg_left hfloor.le hβ.le
    field_simp [hH.ne']
    nlinarith
  have hpower : Real.exp (-β * (m : ℝ) / H) ≤ Real.exp 1 * P ^ (-β) := by
    calc
      _ ≤ Real.exp (-β * Real.log P + β / H) := Real.exp_le_exp.mpr hbase
      _ = Real.exp (β / H) * P ^ (-β) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hP0]
        rw [show -β * Real.log P = Real.log P * (-β) by ring, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr ((div_le_one hH).mpr hβH)) (Real.rpow_nonneg hP0.le _)
  have hgap : 0 < 1 - Real.exp (-β / H) := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith : -β < 0) hH))
  have hden : 1 / (1 - Real.exp (-β / H)) ≤ 2 / (β / H) := by
    simpa only [neg_div] using mrt_geometric_denominator_bound (div_pos hβ hH)
      ((div_le_one hH).mpr hβH)
  calc
    _ ≤ Real.exp (-β * (m : ℝ) / H) / (1 - Real.exp (-β / H)) :=
      mrt_exp_geometric_sum hβ hH m n
    _ ≤ (Real.exp 1 * P ^ (-β)) * (2 / (β / H)) := by
      rw [div_eq_mul_inv, ← one_div]
      exact mul_le_mul hpower hden (le_of_lt (one_div_pos.mpr hgap)) (by positivity)
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

end TwoPointCorrelations

end OAI
