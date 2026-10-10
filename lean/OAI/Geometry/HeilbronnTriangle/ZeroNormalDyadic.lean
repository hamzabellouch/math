import OAI.Geometry.HeilbronnTriangle.AnisotropicDyadic
import OAI.Geometry.HeilbronnTriangle.WeightedNormalReduction

namespace OAI


namespace Problem355.PrimitiveNormal

open Matrix
open scoped Matrix BigOperators

theorem weighted_count_le_of_normal_shell_bound
    (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ) (hW : ∀ A ∈ S, 0 ≤ W A)
    (hdet : ∀ A ∈ S, A.det = 0) (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (X : ℤ) (hX : 1 ≤ X) (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ X)
    {K : ℝ} (hK : 0 ≤ K)
    (hshell : ∀ i : ℕ,
      ∑ w ∈ (normalBox X).filter (fun w =>
        (2 : ℝ) ^ i ≤ ‖toEuclidean w‖ ∧ ‖toEuclidean w‖ < 2 ^ (i + 1)),
        ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A ≤ K) :
    ∑ A ∈ S, W A ≤ K * (Real.log (12 * (X : ℝ) ^ 2) / Real.log 2) := by
  classical
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hR : (1 : ℝ) ≤ 6 * (X : ℝ) ^ 2 := by nlinarith
  have hagg := Anisotropic.sum_le_of_single_dyadic_shell_estimates
    (normalBox X) (fun w => ‖toEuclidean w‖)
    (fun w => ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A)
    hR hK
    (fun w _ => Finset.sum_nonneg (fun A hA => hW A (Finset.mem_filter.mp hA).1))
    (fun w hw => normalBox_norm_bounds hw) hshell
  have hcover := weighted_count_le_sum_normal_fibers S W hW hdet hheight hproj
    X (by omega) hbound
  simpa only [show (2 : ℝ) * (6 * (X : ℝ) ^ 2) = 12 * (X : ℝ) ^ 2 by ring] using
    hcover.trans hagg

lemma normal_range_log_le {X : ℝ} (hX : 1 ≤ X) :
    Real.log (12 * X ^ 2) / Real.log 2 ≤
      4 * (Real.log (2 * X) / Real.log 2) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpos : 0 < 12 * X ^ 2 := by positivity
  have hsq : 1 ≤ X ^ 2 := by nlinarith
  have hfour : 12 * X ^ 2 ≤ (2 * X) ^ 4 := by
    nlinarith [sq_nonneg (X ^ 2 - 1)]
  have hlog := Real.log_le_log hpos hfour
  rw [Real.log_pow] at hlog
  have hquot := div_le_div_of_nonneg_right hlog hlog2.le
  simpa [mul_div_assoc] using hquot

theorem weighted_count_le_log_of_normal_shell_bound
    (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ) (hW : ∀ A ∈ S, 0 ≤ W A)
    (hdet : ∀ A ∈ S, A.det = 0) (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (X : ℤ) (hX : 1 ≤ X) (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ X)
    {K : ℝ} (hK : 0 ≤ K)
    (hshell : ∀ i : ℕ,
      ∑ w ∈ (normalBox X).filter (fun w =>
        (2 : ℝ) ^ i ≤ ‖toEuclidean w‖ ∧ ‖toEuclidean w‖ < 2 ^ (i + 1)),
        ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A ≤ K) :
    ∑ A ∈ S, W A ≤ 4 * K * (Real.log (2 * (X : ℝ)) / Real.log 2) := by
  have h := weighted_count_le_of_normal_shell_bound S W hW hdet hheight hproj
    X hX hbound hK hshell
  have hxR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hmul := mul_le_mul_of_nonneg_left (normal_range_log_le hxR) hK
  calc
    _ ≤ K * (Real.log (12 * (X : ℝ) ^ 2) / Real.log 2) := h
    _ ≤ K * (4 * (Real.log (2 * (X : ℝ)) / Real.log 2)) := hmul
    _ = _ := by ring

end Problem355.PrimitiveNormal

end OAI
