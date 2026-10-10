import OAI.Analysis.HyperbolicCones.PencilBlocks

namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

/-- The finite blocks after splitting the support of the first positive pencil component. -/
structure RawBlockPencil (K : Set Ambient) where
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
  D_identity_posDef : (D 1 : Mat a ℝ).PosDef
  E_identity_posDef : (E 1 : Mat c ℝ).PosDef
  represents : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), ((X, Z), y) ∈ K ↔
    (Matrix.fromBlocks ((D X : Mat a ℝ) + (F Z : Mat a ℝ) + (A y : Mat a ℝ))
      (C Z + B y) (C Z + B y)ᵀ ((E Z : Mat c ℝ) + (G y : Mat c ℝ))).PosSemidef


end Paper256

end

end OAI
