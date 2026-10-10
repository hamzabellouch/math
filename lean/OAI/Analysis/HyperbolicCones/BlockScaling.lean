import OAI.Analysis.HyperbolicCones.BlockReduction
import OAI.Analysis.HyperbolicCones.ScalingAlgebra

namespace OAI

noncomputable section

open Matrix Set
open scoped Matrix.Norms.L2Operator

namespace Paper256.BlockPencil

theorem scaled_congruence {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef))
    (X Z : Sym 4) (y : Fin 3 → ℝ) (s : ℝ) (hs : s ≠ 0) :
    blockScalar P.a P.c s⁻¹ * P.matrix X (s ^ 2 • Z) (s • y) * blockScalar P.a P.c s⁻¹ =
      P.scaled X Z y s := by
  have hG := P.G_eq_zero hSlice y
  simpa [matrix, scaled, hG] using
    block_scaling_identity (P.D X : Mat P.a ℝ) (P.A y : Mat P.a ℝ)
      (P.F Z : Mat P.a ℝ) (P.B y) (P.C Z) (P.E Z : Mat P.c ℝ) s hs

theorem scaled_posSemidef_iff {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef))
    (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef) (s : ℝ) (hs : s ≠ 0) :
    (P.scaled X Z y s).PosSemidef ↔
      ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef := by
  let R := blockScalar P.a P.c s⁻¹
  have hR : IsUnit R := blockScalar_isUnit P.a P.c s⁻¹ (inv_ne_zero hs)
  have hRt : Rᴴ = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      blockScalar_transpose P.a P.c s⁻¹
  calc
    (P.scaled X Z y s).PosSemidef ↔ (P.matrix X (s ^ 2 • Z) (s • y)).PosSemidef := by
      rw [← P.scaled_congruence hSlice X Z y s hs]
      simpa only [Matrix.star_eq_conjTranspose, hRt] using
        hR.posSemidef_star_right_conjugate_iff (x := P.matrix X (s ^ 2 • Z) (s • y))
    _ ↔ (((X, s ^ 2 • Z), s • y) : Ambient) ∈ K :=
      (P.represents X (s ^ 2 • Z) (s • y)).symm
    _ ↔ (s ^ 2 • ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹)).PosSemidef := by
      rw [hSlice X (s ^ 2 • Z) (s • y) hX]
      simp only [selfAdjoint.val_smul, phi_scaling, smul_sub]
    _ ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef := by
      exact posSemidef_smul_iff (sq_pos_of_ne_zero hs)

end Paper256.BlockPencil

end

end OAI
