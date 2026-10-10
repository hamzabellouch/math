import OAI.Analysis.HyperbolicCones.MatrixLinear

namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

/-- The actual finite blocks after common-kernel compression and fixed diagonal congruence. -/
structure BlockPencil (K : Set Ambient) where
  a : ℕ
  c : ℕ
  a_pos : 0 < a
  c_pos : 0 < c
  D : Sym 4 →ₗ[ℝ] Sym a
  E : Sym 4 →ₗ[ℝ] Sym c
  F : Sym 4 →ₗ[ℝ] Sym a
  C : Sym 4 →ₗ[ℝ] Matrix (Fin a) (Fin c) ℝ
  A : (Fin 3 → ℝ) →ₗ[ℝ] Sym a
  B : (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin a) (Fin c) ℝ
  G : (Fin 3 → ℝ) →ₗ[ℝ] Sym c
  D_positive : ∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef → (D X : Mat a ℝ).PosSemidef
  E_positive : ∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef → (E X : Mat c ℝ).PosSemidef
  D_unital : D 1 = 1
  E_unital : E 1 = 1
  represents : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), ((X, Z), y) ∈ K ↔
    (Matrix.fromBlocks ((D X : Mat a ℝ) + (F Z : Mat a ℝ) + (A y : Mat a ℝ))
      (C Z + B y) (C Z + B y)ᵀ ((E Z : Mat c ℝ) + (G y : Mat c ℝ))).PosSemidef

namespace BlockPencil

def matrix {K : Set Ambient} (P : BlockPencil K) (X Z : Sym 4) (y : Fin 3 → ℝ) :
    Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ :=
  Matrix.fromBlocks ((P.D X : Mat P.a ℝ) + (P.F Z : Mat P.a ℝ) + (P.A y : Mat P.a ℝ))
    (P.C Z + P.B y) (P.C Z + P.B y)ᵀ ((P.E Z : Mat P.c ℝ) + (P.G y : Mat P.c ℝ))

def scaled {K : Set Ambient} (P : BlockPencil K) (X Z : Sym 4) (y : Fin 3 → ℝ) (s : ℝ) :
    Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ :=
  Matrix.fromBlocks ((P.D X : Mat P.a ℝ) + s • (P.A y : Mat P.a ℝ) +
      s ^ 2 • (P.F Z : Mat P.a ℝ))
    (P.B y + s • P.C Z) (P.B y + s • P.C Z)ᵀ (P.E Z : Mat P.c ℝ)

def limit {K : Set Ambient} (P : BlockPencil K) (X Z : Sym 4) (y : Fin 3 → ℝ) :
    Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ :=
  Matrix.fromBlocks (P.D X : Mat P.a ℝ) (P.B y) (P.B y)ᵀ (P.E Z : Mat P.c ℝ)

theorem matrix_isHermitian {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) : (P.matrix X Z y).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · exact ((P.D X).property.add (P.F Z).property).add (P.A y).property
  · simp
  · exact (P.E Z).property.add (P.G y).property

theorem limit_isHermitian {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) : (P.limit X Z y).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · exact (P.D X).property
  · simp
  · exact (P.E Z).property

end BlockPencil

end Paper256

end

end OAI
