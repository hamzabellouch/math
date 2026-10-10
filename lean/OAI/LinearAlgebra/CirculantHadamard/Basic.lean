import OAI.LinearAlgebra.CirculantHadamard.Model

namespace OAI

universe uR

namespace CirculantHadamard

def rowCirculant {n : ℕ} {R : Type uR} (h : Fin n → R) :
    Matrix (Fin n) (Fin n) R := fun i j => h (j - i)

@[simp] theorem rowCirculant_apply {n : ℕ} {R : Type uR}
    (h : Fin n → R) (i j : Fin n) : rowCirculant h i j = h (j - i) := rfl

theorem rowCirculant_isCirculant {n : ℕ} (h : Fin n → ℝ) :
    IsCirculant (rowCirculant h) := ⟨h, fun _ _ => rfl⟩

@[simp] theorem rowCirculant_zero_row {n : ℕ} [NeZero n]
    {R : Type uR} (h : Fin n → R) (j : Fin n) : rowCirculant h 0 j = h j := by
  simp [rowCirculant]

end CirculantHadamard

end OAI
