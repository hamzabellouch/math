import OAI.Geometry.EinsteinFour.HighestHessian

namespace OAI

/-! Linearity of the concrete highest-Hessian coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

private theorem entries_add_0 (c d : Fin 21 → ℝ) :
    entries (c + d) 0 = entries c 0 + entries d 0 := by
  ext i j
  change entries (c + d) 0 i j = entries c 0 i j + entries d 0 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_add_1 (c d : Fin 21 → ℝ) :
    entries (c + d) 1 = entries c 1 + entries d 1 := by
  ext i j
  change entries (c + d) 1 i j = entries c 1 i j + entries d 1 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_add_2 (c d : Fin 21 → ℝ) :
    entries (c + d) 2 = entries c 2 + entries d 2 := by
  ext i j
  change entries (c + d) 2 i j = entries c 2 i j + entries d 2 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_add_3 (c d : Fin 21 → ℝ) :
    entries (c + d) 3 = entries c 3 + entries d 3 := by
  ext i j
  change entries (c + d) 3 i j = entries c 3 i j + entries d 3 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_add_4 (c d : Fin 21 → ℝ) :
    entries (c + d) 4 = entries c 4 + entries d 4 := by
  ext i j
  change entries (c + d) 4 i j = entries c 4 i j + entries d 4 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_add_5 (c d : Fin 21 → ℝ) :
    entries (c + d) 5 = entries c 5 + entries d 5 := by
  ext i j
  change entries (c + d) 5 i j = entries c 5 i j + entries d 5 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_add_6 (c d : Fin 21 → ℝ) :
    entries (c + d) 6 = entries c 6 + entries d 6 := by
  ext i j
  change entries (c + d) 6 i j = entries c 6 i j + entries d 6 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_add_7 (c d : Fin 21 → ℝ) :
    entries (c + d) 7 = entries c 7 + entries d 7 := by
  ext i j
  change entries (c + d) 7 i j = entries c 7 i j + entries d 7 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_add_8 (c d : Fin 21 → ℝ) :
    entries (c + d) 8 = entries c 8 + entries d 8 := by
  ext i j
  change entries (c + d) 8 i j = entries c 8 i j + entries d 8 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_add_9 (c d : Fin 21 → ℝ) :
    entries (c + d) 9 = entries c 9 + entries d 9 := by
  ext i j
  change entries (c + d) 9 i j = entries c 9 i j + entries d 9 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_smul_0 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 0 = r • entries c 0 := by
  ext i j
  change entries (r • c) 0 i j = r * entries c 0 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_smul_1 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 1 = r • entries c 1 := by
  ext i j
  change entries (r • c) 1 i j = r * entries c 1 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_smul_2 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 2 = r • entries c 2 := by
  ext i j
  change entries (r • c) 2 i j = r * entries c 2 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_smul_3 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 3 = r • entries c 3 := by
  ext i j
  change entries (r • c) 3 i j = r * entries c 3 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_smul_4 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 4 = r • entries c 4 := by
  ext i j
  change entries (r • c) 4 i j = r * entries c 4 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_smul_5 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 5 = r • entries c 5 := by
  ext i j
  change entries (r • c) 5 i j = r * entries c 5 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_smul_6 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 6 = r • entries c 6 := by
  ext i j
  change entries (r • c) 6 i j = r * entries c 6 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_smul_7 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 7 = r • entries c 7 := by
  ext i j
  change entries (r • c) 7 i j = r * entries c 7 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_smul_8 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 8 = r • entries c 8 := by
  ext i j
  change entries (r • c) 8 i j = r * entries c 8 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

private theorem entries_smul_9 (r : ℝ) (c : Fin 21 → ℝ) :
    entries (r • c) 9 = r • entries c 9 := by
  ext i j
  change entries (r • c) 9 i j = r * entries c 9 i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates]
  all_goals ring

theorem entries_add (c d : Fin 21 → ℝ) : entries (c + d) = entries c + entries d := by
  funext k
  fin_cases k
  · exact entries_add_0 c d
  · exact entries_add_1 c d
  · exact entries_add_2 c d
  · exact entries_add_3 c d
  · exact entries_add_4 c d
  · exact entries_add_5 c d
  · exact entries_add_6 c d
  · exact entries_add_7 c d
  · exact entries_add_8 c d
  · exact entries_add_9 c d

theorem entries_smul (r : ℝ) (c : Fin 21 → ℝ) : entries (r • c) = r • entries c := by
  funext k
  fin_cases k
  · exact entries_smul_0 r c
  · exact entries_smul_1 r c
  · exact entries_smul_2 r c
  · exact entries_smul_3 r c
  · exact entries_smul_4 r c
  · exact entries_smul_5 r c
  · exact entries_smul_6 r c
  · exact entries_smul_7 r c
  · exact entries_smul_8 r c
  · exact entries_smul_9 r c

theorem symmetricArray_add (a b : Fin 10 → Mat) :
    symmetricArray (a + b) = symmetricArray a + symmetricArray b := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem symmetricArray_smul (r : ℝ) (a : Fin 10 → Mat) :
    symmetricArray (r • a) = r • symmetricArray a := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem highest_add (c d : Fin 21 → ℝ) : highest (c + d) = highest c + highest d := by
  unfold highest
  rw [entries_add, symmetricArray_add]

theorem highest_smul (r : ℝ) (c : Fin 21 → ℝ) : highest (r • c) = r • highest c := by
  unfold highest
  rw [entries_smul, symmetricArray_smul]


end
end PositiveEinsteinFour.HighestHessian

end OAI
