import Mathlib

namespace OAI

noncomputable section

namespace KKVariableUltra

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def diagonalProjection {n : ℕ} (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => if i∈S then 1 else 0)

theorem diagonalProjection_isProjection {n : ℕ} (S : Finset (Fin n)) :
    IsStarProjection (diagonalProjection S) := by
  classical
  constructor
  · change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    split_ifs <;> simp
  · ext i j
    simp only [diagonalProjection,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp_all

theorem diagonalProjection_trace {n : ℕ} (S : Finset (Fin n)) :
    Matrix.trace (diagonalProjection S)=(S.card:ℂ) := by
  classical
  simp [diagonalProjection,Matrix.trace_diagonal]

omit [StarOrderedRing A] in
theorem matrix_range_projection (n r : ℕ) (hr : r≤n)
    (ρ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] A) (τ : A →ₚ[ℂ] ℂ)
    (hτ : ∀ x, τ (ρ x)=(n:ℂ)⁻¹*Matrix.trace x) :
    ∃ p : A, p∈ρ.range ∧ IsStarProjection p ∧ ‖p‖≤1 ∧ τ p=(n:ℂ)⁻¹*(r:ℂ) := by
  classical
  obtain ⟨S,_,hScard⟩ := Finset.exists_subset_card_eq (s := Finset.univ (α := Fin n))
    (by simpa using hr)
  let p := ρ (diagonalProjection S)
  have hp : IsStarProjection p := (diagonalProjection_isProjection S).map ρ
  refine ⟨p,⟨diagonalProjection S,rfl⟩,hp,hp.norm_le,?_⟩
  change τ (ρ (diagonalProjection S))=_
  rw [hτ,diagonalProjection_trace,hScard]

end

end KKVariableUltra
end

end OAI
