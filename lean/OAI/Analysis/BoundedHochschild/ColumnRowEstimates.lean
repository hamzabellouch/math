import OAI.Analysis.BoundedHochschild.MatrixAmplification

namespace OAI

/-! Finite row and column estimates inside a properly infinite algebra. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] {n : ℕ}
variable (c : Fin n → PartialIso M) (hi : ∀ i, (c i).initial = 1)
  (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)

/-- A row, realized inside the algebra by orthogonal isometries. -/
def columnRow (x : Fin n → M) : M := ∑ i, x i * star (c i : M)

/-- A column, realized inside the algebra by orthogonal isometries. -/
def columnColumn (y : Fin n → M) : M := ∑ i, (c i : M) * y i

include hi ho in
lemma columnRow_mul_column (x y : Fin n → M) :
    columnRow c x * columnColumn c y = ∑ i, x i * y i := by
  classical
  calc
    _ = ∑ i, ∑ j, x i * (star (c i : M) * (c j : M)) * y j := by
      simp only [columnRow, columnColumn]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [mul_assoc]
    _ = _ := by simp [column_star_mul c hi ho]

include hi ho in
lemma columnRow_mul_star (x : Fin n → M) :
    columnRow c x * star (columnRow c x) = ∑ i, x i * star (x i) := by
  have hs : star (columnRow c x) = columnColumn c (fun i => star (x i)) := by
    simp only [columnRow, columnColumn, star_sum, star_mul, star_star]
  rw [hs, columnRow_mul_column c hi ho]

include hi ho in
lemma star_column_mul_column (y : Fin n → M) :
    star (columnColumn c y) * columnColumn c y = ∑ i, star (y i) * y i := by
  have hs : star (columnColumn c y) = columnRow c (fun i => star (y i)) := by
    simp only [columnRow, columnColumn, star_sum, star_mul]
  rw [hs, columnRow_mul_column c hi ho]

include hi ho in
lemma columnRow_norm_sq (x : Fin n → M) :
    ‖columnRow c x‖ ^ 2 = ‖∑ i, x i * star (x i)‖ := by
  rw [sq, ← CStarRing.norm_self_mul_star, columnRow_mul_star c hi ho]

include hi ho in
lemma columnColumn_norm_sq (y : Fin n → M) :
    ‖columnColumn c y‖ ^ 2 = ‖∑ i, star (y i) * y i‖ := by
  rw [sq, ← CStarRing.norm_star_mul_self, star_column_mul_column c hi ho]

include hi ho in
/-- The finite row-column inequality, using only the particular isometries
available in the properly infinite case. -/
lemma finite_row_column_estimate (x y : Fin n → M) :
    ‖∑ i, x i * y i‖ ^ 2 ≤ ‖∑ i, x i * star (x i)‖ * ‖∑ i, star (y i) * y i‖ := by
  rw [← columnRow_mul_column c hi ho]
  calc
    _ ≤ (‖columnRow c x‖ * ‖columnColumn c y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_mul_le _ _) 2
    _ = _ := by rw [mul_pow, columnRow_norm_sq c hi ho, columnColumn_norm_sq c hi ho]

end BoundedHochschild.KadisonRingrose

end

end OAI
