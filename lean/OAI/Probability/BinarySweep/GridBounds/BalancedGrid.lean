import Mathlib
import OAI.Probability.BinarySweep.SparseBounds.FewSparseBases

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open GridSplit

lemma balanced_counts (b : ℕ) (hb : 2 ≤ b) : ∃m n : ℕ,
    b=m+n ∧ 1 ≤ m ∧ 1 ≤ n ∧ m < b ∧ n < b ∧ m ≤ 2*n ∧ n ≤ 2*m := by
  refine ⟨b/2,b-b/2,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

lemma balanced_grid_bounds {m n r : ℕ} (bits : Fin (m+n) → ℕ)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≤ 2*n) (hnm : n ≤ 2*m)
    (hd : ∀j,r ≤ bits j ∧ bits j ≤ 2*r) (hr : 400000000 ≤ (r:ℝ)*Real.log 2) :
    1 ≤ Real.log (gridSize (leftBits bits)) ∧ 1 ≤ Real.log (gridSize (rightBits bits)) ∧
    Real.log (gridSize (leftBits bits)) ≤ (4/5:ℝ)*Real.log (gridSize bits) ∧
    Real.log (gridSize (rightBits bits)) ≤ (4/5:ℝ)*Real.log (gridSize bits) ∧
    Real.log 4*(m+n) ≤ (1/1000:ℝ)*Real.log (gridSize bits) := by
  have hl := grid_log_lower (fun j : Fin m => (hd (j.castAdd n)).1)
  have hr' := grid_log_lower (fun j : Fin n => (hd (j.natAdd m)).1)
  have hlu := grid_log_upper (fun j : Fin m => (hd (j.castAdd n)).2)
  have hru := grid_log_upper (fun j : Fin n => (hd (j.natAdd m)).2)
  change (m:ℝ)*((r:ℝ)*Real.log 2) ≤ Real.log (gridSize (leftBits bits)) at hl
  change (n:ℝ)*((r:ℝ)*Real.log 2) ≤ Real.log (gridSize (rightBits bits)) at hr'
  change Real.log (gridSize (leftBits bits)) ≤ (m:ℝ)*(2*r*Real.log 2) at hlu
  change Real.log (gridSize (rightBits bits)) ≤ (n:ℝ)*(2*r*Real.log 2) at hru
  have hsum : Real.log (gridSize bits)=Real.log (gridSize (leftBits bits))+Real.log (gridSize (rightBits bits)) := by
    rw [size_split,Nat.cast_mul]
    exact Real.log_mul (by exact_mod_cast (gridSize_pos (leftBits bits)).ne')
      (by exact_mod_cast (gridSize_pos (rightBits bits)).ne')
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hmnR : (m:ℝ) ≤ 2*n := by exact_mod_cast hmn
  have hnmR : (n:ℝ) ≤ 2*m := by exact_mod_cast hnm
  have hscale : 0 ≤ (r:ℝ)*Real.log 2 := by linarith
  have hmnl := mul_le_mul_of_nonneg_right hmnR hscale
  have hnml := mul_le_mul_of_nonneg_right hnmR hscale
  have hm1 := mul_le_mul_of_nonneg_right hmR hscale
  have hn1 := mul_le_mul_of_nonneg_right hnR hscale
  have haxes := grid_log_lower (fun j => (hd j).1)
  have hlog4 : Real.log 4 ≤ 4 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)).trans (by norm_num)
  have hbR : (0:ℝ) ≤ m+n := by positivity
  have hax := mul_le_mul_of_nonneg_right hlog4 hbR
  have hsc := mul_le_mul_of_nonneg_left hr hbR
  push_cast at haxes
  refine ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

end BinaryCoordinateSweeps

end

end OAI
