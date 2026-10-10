import OAI.Analysis.KadisonKastler.CompletelyBounded
import OAI.Analysis.KadisonKastler.RectangularCorner
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI

/-! # Rectangular complete bounds from square levels of size at least two -/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Reindexing transports a bound at a finite ordinal to any finite square
matrix of the same size. -/
theorem norm_map_square_of_fin (F : A →ₗ[ℂ] B) {c : ℝ}
    (hsquare : ∀ n : ℕ, 2 ≤ n → ∀ X : CStarMatrix (Fin n) (Fin n) A,
      ‖CStarMatrix.mapₗ F X‖ ≤ c * ‖X‖)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : 2 ≤ Fintype.card ι)
    (X : CStarMatrix ι ι A) : ‖CStarMatrix.mapₗ F X‖ ≤ c * ‖X‖ := by
  let e := Fintype.equivFin ι
  let eA := CStarMatrix.reindexₐ ℂ A e
  let eB := CStarMatrix.reindexₐ ℂ B e
  have h := hsquare (Fintype.card ι) hι (eA X)
  have heq : CStarMatrix.mapₗ F (eA X) = eB (CStarMatrix.mapₗ F X) := rfl
  have hnA : ‖eA X‖ = ‖X‖ :=
    NonUnitalStarAlgHom.norm_map eA.toStarAlgHom eA.injective X
  have hnB : ‖eB (CStarMatrix.mapₗ F X)‖ = ‖CStarMatrix.mapₗ F X‖ :=
    NonUnitalStarAlgHom.norm_map eB.toStarAlgHom eB.injective (CStarMatrix.mapₗ F X)
  rw [heq, hnA, hnB] at h
  exact h

/-- Positive rectangular sizes embed isometrically into a square of size
at least two; zero rectangular sizes contribute only the zero matrix. -/
theorem completelyBoundedBy_of_large_square (F : A →ₗ[ℂ] B) {c : ℝ}
    (hsquare : ∀ n : ℕ, 2 ≤ n → ∀ X : CStarMatrix (Fin n) (Fin n) A,
      ‖CStarMatrix.mapₗ F X‖ ≤ c * ‖X‖) : CompletelyBoundedBy F c := by
  classical
  intro p q X
  by_cases hp : p = 0
  · subst p
    have hX : X = 0 := by ext i; exact Fin.elim0 i
    simp only [hX, map_zero, norm_zero, mul_zero, le_refl]
  by_cases hq : q = 0
  · subst q
    have hX : X = 0 := by ext i j; exact Fin.elim0 j
    simp only [hX, map_zero, norm_zero, mul_zero, le_refl]
  have hcard : 2 ≤ Fintype.card (Fin p ⊕ Fin q) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have h := norm_map_square_of_fin F hsquare hcard (rectangularCorner X)
  rw [← rectangularCorner_map, norm_rectangularCorner, norm_rectangularCorner] at h
  exact h

end

end KadisonKastler

end OAI
