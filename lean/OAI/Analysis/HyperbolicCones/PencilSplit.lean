import OAI.Analysis.HyperbolicCones.SplitAssembly
import OAI.Analysis.HyperbolicCones.BlockNormalization

namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem rawBlockPencil_exists {m : ℕ} (K : Set Ambient)
    (C : Ambient →ₗ[ℝ] Sym m) (hC : (C basePoint : Mat m ℝ).PosDef)
    (hrep : K = {x | (C x : Mat m ℝ).PosSemidef})
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    Nonempty (RawBlockPencil K) := by
  classical
  let A := pencilFirst C 1
  have hfirst := (pencil_components_positive K C hrep hzero).1
  have hA : (A : Mat m ℝ).PosSemidef := hfirst 1 Matrix.PosSemidef.one
  obtain ⟨S⟩ := pencilSpectralSplit_exists A hA
    (pencil_first_identity_ne_zero K C hrep hzero)
    (pencil_first_identity_not_posDef K C hrep hzero)
  let U : Mat m ℝ := (sym_isHermitian A).eigenvectorUnitary
  have hU : IsUnit U := Unitary.isUnit_coe (U := (sym_isHermitian A).eigenvectorUnitary)
  let L := conjugatePencil C U
  have hrepL : K = {x | (L x : Mat m ℝ).PosSemidef} := by
    ext x
    rw [hrep]
    exact (conjugatePencil_posSemidef_iff C U hU x).symm
  have hpos := pencil_components_positive K L hrepL hzero
  have hrow (X : Sym 4) (i : Fin S.c) (j : Fin m) :
      (pencilFirst L X : Mat m ℝ) (S.index (Sum.inr i)) j = 0 := by
    exact spectral_conjugate_zero_row A (pencilFirst C X) hA
      (positiveLinearMap_common_kernel (pencilFirst C) hfirst X)
      _ (S.nonpositive i) j
  let f := S.index ∘ Sum.inl
  let g := S.index ∘ Sum.inr
  have hf : Function.Injective f := S.index.injective.comp Sum.inl_injective
  have hg : Function.Injective g := S.index.injective.comp Sum.inr_injective
  have hD : ((pencilFirst L 1 : Mat m ℝ).submatrix f f).PosDef := by
    change ((Uᴴ * (A : Mat m ℝ) * U).submatrix f f).PosDef
    rw [spectral_conjugate_diagonal A, Matrix.submatrix_diagonal _ f hf]
    exact Matrix.PosDef.diagonal S.positive
  have hbase : (L basePoint : Mat m ℝ).PosDef := conjugatePencil_posDef C U hU basePoint hC
  have hE : ((pencilSecond L 1 : Mat m ℝ).submatrix g g).PosDef := by
    have heq : (L basePoint : Mat m ℝ).submatrix g g =
        (pencilSecond L 1 : Mat m ℝ).submatrix g g := by
      ext i j
      change (L (((1, 1), 0) : Ambient) : Mat m ℝ) (g i) (g j) = _
      rw [pencil_decomposition]
      change (pencilFirst L 1 : Mat m ℝ) (g i) (g j) +
        (pencilSecond L 1 : Mat m ℝ) (g i) (g j) +
        (pencilParameter L 0 : Mat m ℝ) (g i) (g j) = _
      rw [map_zero]
      change (pencilFirst L 1 : Mat m ℝ) (S.index (Sum.inr i)) (g j) +
        (pencilSecond L 1 : Mat m ℝ) (g i) (g j) + 0 =
        (pencilSecond L 1 : Mat m ℝ) (g i) (g j)
      rw [hrow, zero_add, add_zero]
    rw [← heq]
    exact hbase.submatrix hg
  exact rawBlockPencil_of_partition K L S.a_pos S.c_pos S.index hrepL
    hpos.1 hpos.2 hrow hD hE

theorem blockPencil_exists (K : Set Ambient) (m : ℕ) (_hm : 0 < m)
    (C : Ambient →ₗ[ℝ] Sym m) (hC : (C basePoint : Mat m ℝ).PosDef)
    (hrep : K = {x | (C x : Mat m ℝ).PosSemidef})
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    Nonempty (BlockPencil K) := by
  obtain ⟨P⟩ := rawBlockPencil_exists K C hC hrep hzero
  exact ⟨P.normalize⟩

end Paper256

end

end OAI
