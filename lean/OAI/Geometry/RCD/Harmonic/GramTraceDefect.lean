import OAI.Geometry.RCD.Coordinates.BochnerFrameDefect

namespace OAI

/-! # Trace and square moments controlled by the original Gram defect -/

open Finset
noncomputable section
namespace RegularPointCoordinates

def matrixGramDefect {n : ℕ} (G : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, |G i j-(if i=j then 1 else 0)|

theorem matrixGramDefect_nonneg {n : ℕ} (G : Fin n → Fin n → ℝ) :
    0≤ matrixGramDefect G := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => abs_nonneg _))

theorem gram_trace_defect {n : ℕ} (G : Fin n → Fin n → ℝ) :
    |∑ i, G i i-(n:ℝ)|≤ matrixGramDefect G := by
  classical
  have he : (∑ i, G i i)-(n:ℝ)=∑ i, (G i i-1) := by simp [sum_sub_distrib]
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i _
  have hh := single_le_sum (s := (univ : Finset (Fin n)))
    (f := fun j => |G i j-(if i=j then 1 else 0)|) (fun _ _ => abs_nonneg _) (mem_univ i)
  simpa only [ite_true] using hh

theorem gram_square_defect {n : ℕ} (G : Fin n → Fin n → ℝ) {C : ℝ}
    (hG : ∀ i j, |G i j|≤C) :
    |∑ i, ∑ j, (G i j)^2-(n:ℝ)|≤(C+1)*matrixGramDefect G := by
  classical
  have he : (∑ i, ∑ j, (G i j)^2)-(n:ℝ)=
      ∑ i, ∑ j, ((G i j)^2-(if i=j then 1 else 0)) := by
    simp [sum_sub_distrib]
  have hterm (i j : Fin n) : |(G i j)^2-(if i=j then 1 else 0)|≤
      (C+1)*|G i j-(if i=j then 1 else 0)| := by
    let d : ℝ := if i=j then 1 else 0
    have hd : |d|≤1 := by dsimp [d]; split_ifs <;> norm_num
    have hsum : |G i j+d|≤C+1 := (abs_add_le _ _).trans (add_le_add (hG i j) hd)
    have hsq : (G i j)^2-d=(G i j-d)*(G i j+d) := by
      dsimp [d]
      split_ifs <;> ring
    change |(G i j)^2-d|≤(C+1)*|G i j-d|
    rw [hsq,abs_mul,mul_comm (C+1)]
    exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
  rw [he]
  calc
    _≤∑ i, |∑ j, ((G i j)^2-(if i=j then 1 else 0))| := abs_sum_le_sum_abs _ _
    _≤∑ i, ∑ j, |(G i j)^2-(if i=j then 1 else 0)| :=
      sum_le_sum (fun _ _ => abs_sum_le_sum_abs _ _)
    _≤∑ i, ∑ j, (C+1)*|G i j-(if i=j then 1 else 0)| :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => hterm i j))
    _=(C+1)*matrixGramDefect G := by simp only [matrixGramDefect,mul_sum]

end RegularPointCoordinates

end

end OAI
