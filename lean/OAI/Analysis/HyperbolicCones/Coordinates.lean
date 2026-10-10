import OAI.Analysis.HyperbolicCones.Model

namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace Paper256

theorem symIndex_card : Fintype.card SymIndex = 10 := by decide

theorem coordinate_card : Fintype.card Coord = 23 := by decide

theorem symmetricCoordinates_isHermitian (v : SymIndex → ℝ) :
    (symmetricCoordinates v).IsHermitian := by
  change (symmetricCoordinates v)ᴴ = symmetricCoordinates v
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have h : i = j := le_antisymm hij hji
      subst j
      rfl
    · simp [symmetricCoordinates, hij, hji]
  · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
    simp [symmetricCoordinates, hij, hji]

def symmetricCoordinateEquiv : Sym 4 ≃ₗ[ℝ] (SymIndex → ℝ) where
  toFun X ij := (X : Mat 4 ℝ) ij.val.1 ij.val.2
  invFun v := ⟨symmetricCoordinates v, symmetricCoordinates_isHermitian v⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    by_cases h : i ≤ j
    · simp [symmetricCoordinates, h]
    · have hX : (X : Mat 4 ℝ).IsHermitian := X.property
      simpa [symmetricCoordinates, h] using hX.apply i j
  right_inv v := by
    funext ij
    simp [symmetricCoordinates, ij.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem symmetric_finrank : Module.finrank ℝ (Sym 4) = 10 := by
  rw [symmetricCoordinateEquiv.finrank_eq]
  simp [symIndex_card]

theorem ambient_finrank : Module.finrank ℝ Ambient = 23 := by
  simp [Ambient, Module.finrank_prod, symmetric_finrank]

end Paper256

end

end OAI
