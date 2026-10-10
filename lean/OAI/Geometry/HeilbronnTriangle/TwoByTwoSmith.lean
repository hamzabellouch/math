import OAI.Geometry.HeilbronnTriangle.PrimePowerFactors
import OAI.Geometry.HeilbronnTriangle.DividingPivot
import OAI.Geometry.HeilbronnTriangle.TwoByTwoPivot

namespace OAI


namespace Problem355.TwoByTwoSmith
variable {R : Type*} [CommRing R]

def diagonalUnit (u v : Rˣ) : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := Matrix.diagonal ![(u : R), (v : R)]
  inv := Matrix.diagonal ![(↑(u⁻¹) : R), (↑(v⁻¹) : R)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply]

theorem diagonal_factor (x y : R) (u v : Rˣ) :
    Matrix.diagonal ![x * ↑u, y * ↑v] =
      Matrix.diagonal ![x, y] * (diagonalUnit u v : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalUnit, Matrix.mul_apply, Matrix.diagonal_apply]

theorem exists_ordered_diagonal (A : Matrix (Fin 2) (Fin 2) R)
    (h : ∃ i j, ∀ a b, A i j ∣ A a b) :
    ∃ (x y : R) (P Q : (Matrix (Fin 2) (Fin 2) R)ˣ),
      x ∣ y ∧ A = (P : Matrix (Fin 2) (Fin 2) R) *
        Matrix.diagonal ![x, y] * (Q : Matrix (Fin 2) (Fin 2) R) := by
  obtain ⟨i, j, hij⟩ := h
  obtain ⟨S, T, hpivot, hdiv⟩ := TwoByTwoPivot.move_dividing_entry A i j hij
  let C := (S : Matrix (Fin 2) (Fin 2) R) * A * (T : Matrix (Fin 2) (Fin 2) R)
  obtain ⟨d, P, Q, hd, hfac⟩ := DividingPivot.exists_dividing_pivot_factorization C hdiv
  refine ⟨C 0 0, d, S⁻¹ * P, Q * T⁻¹, hd, ?_⟩
  have hu := DividingPivot.undo_reduction S T A
    ((P : Matrix (Fin 2) (Fin 2) R) * Matrix.diagonal ![C 0 0, d] * Q) hfac
  simpa only [Units.val_mul, mul_assoc] using hu

theorem exists_prime_power_diagonal {p : ℕ} (hp : p.Prime) (k : ℕ)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k))) :
    ∃ b e : ℕ, b ≤ e ∧ e ≤ k ∧
      ∃ P Q : (Matrix (Fin 2) (Fin 2) (ZMod (p ^ k)))ˣ,
        A = (P : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k))) *
          Matrix.diagonal ![(p : ZMod (p ^ k)) ^ b, (p : ZMod (p ^ k)) ^ e] *
          (Q : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k))) := by
  obtain ⟨ij, hij⟩ := PrimePowerFactors.exists_dvd_all hp k
    (fun ij : Fin 2 × Fin 2 => A ij.1 ij.2)
  obtain ⟨x, y, P, Q, hxy, hfac⟩ := exists_ordered_diagonal A
    ⟨ij.1, ij.2, fun a b => hij (a, b)⟩
  obtain ⟨b, e, hbe, hek, u, v, hx, hy⟩ :=
    PrimePowerFactors.exists_ordered_factors hp k x y hxy
  refine ⟨b, e, hbe, hek, P, diagonalUnit u v * Q, ?_⟩
  rw [hx, hy, diagonal_factor] at hfac
  simpa only [Units.val_mul, mul_assoc] using hfac

end Problem355.TwoByTwoSmith

end OAI
