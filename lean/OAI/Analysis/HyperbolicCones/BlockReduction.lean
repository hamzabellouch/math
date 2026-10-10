import OAI.Analysis.HyperbolicCones.PencilBlocks
import OAI.Analysis.HyperbolicCones.RescalingBasic

namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256.BlockPencil

theorem G_eq_zero {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef))
    (y : Fin 3 → ℝ) : P.G y = 0 := by
  let Z0 : Sym 4 := ⟨phi y (1 : Mat 4 ℝ), phi_isHermitian y 1 Matrix.isHermitian_one⟩
  apply linear_term_zero_of_quadratic_posSemidef (P.E Z0) (P.G y)
  intro s
  have hm : (((1, s ^ 2 • Z0), s • y) : Ambient) ∈ K := by
    apply (hSlice 1 (s ^ 2 • Z0) (s • y) Matrix.PosDef.one).mpr
    simp [Z0, phi_scaling]
    exact Matrix.PosSemidef.zero
  have hp := (P.represents 1 (s ^ 2 • Z0) (s • y)).mp hm
  have hb := hp.submatrix Sum.inr
  convert hb using 1
  ext i j
  simp [Matrix.submatrix, Matrix.fromBlocks]

theorem scaled_isHermitian {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) (s : ℝ) : (P.scaled X Z y s).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · exact ((P.D X).property.add ((IsSelfAdjoint.all s).smul (P.A y).property)).add
      ((IsSelfAdjoint.all (s ^ 2)).smul (P.F Z).property)
  · simp
  · exact (P.E Z).property

theorem scaled_zero {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) : P.scaled X Z y 0 = P.limit X Z y := by
  simp [scaled, limit]

end Paper256.BlockPencil

end

end OAI
