import OAI.Analysis.HyperbolicCones.PencilRecovery
import OAI.Analysis.HyperbolicCones.SpectralBounds

namespace OAI

noncomputable section

open Matrix Set Filter
open scoped Topology Matrix.Norms.L2Operator

namespace Paper256

theorem linear_term_positive_and_negative {n : ℕ} (E G : Sym n)
    (h : ∀ s : ℝ, (s ^ 2 • (E : Mat n ℝ) + s • (G : Mat n ℝ)).PosSemidef) :
    (G : Mat n ℝ).PosSemidef ∧ (-(G : Mat n ℝ)).PosSemidef := by
  have hz := linear_term_zero_of_quadratic_posSemidef E G h
  subst G
  exact ⟨Matrix.PosSemidef.zero, by simpa using (Matrix.PosSemidef.zero (n := Fin n) (R := ℝ))⟩

namespace BlockPencil

theorem limit_add_identity_eq_add {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) (δ : ℝ) :
    P.limit X (Z + δ • 1) y = P.limit X Z y +
      Matrix.fromBlocks (0 : Mat P.a ℝ) 0 0 (δ • (1 : Mat P.c ℝ)) := by
  rw [P.limit_add_identity]
  ext (i | i) (j | j) <;> simp [limit, Matrix.fromBlocks]

theorem scaled_eventually_posDef {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) (hP : (P.limit X Z y).PosDef) :
    ∀ᶠ s : ℝ in 𝓝 0, (P.scaled X Z y s).PosDef := by
  have hnb : {H : selfAdjoint (Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ) |
      (H : Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ).PosDef} ∈
      𝓝 (P.limitSelfAdjoint X Z y) :=
    (FiniteMatrix.isOpen_posDef (Fin P.a ⊕ Fin P.c)).mem_nhds hP
  exact (P.scaled_tendsto X Z y).eventually hnb

theorem regularized_target_of_limit {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef))
    (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef)
    (hM : (P.limit X Z y).PosSemidef) (δ : ℝ) (hδ : 0 < δ) :
    (((Z + δ • 1 : Sym 4) : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef :=
  P.target_of_limit_posSemidef hSlice X (Z + δ • 1) y hX
    (P.limit_add_identity_posDef X Z y hX hM δ hδ).posSemidef

end BlockPencil

end Paper256

end

end OAI
