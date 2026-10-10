import OAI.Analysis.KadisonKastler.FiniteMatrixBounds
import OAI.Analysis.KadisonKastler.Haagerup

namespace OAI

/-! Finite index changes for bilinear amplifications. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The bilinear amplification with arbitrary finite index types. -/
def finiteBilinearProduct (f : A →ₗ[ℂ] A →ₗ[ℂ] A)
    {ι κ τ : Type*} [Fintype κ] (X : CStarMatrix ι κ A) (Y : CStarMatrix κ τ A) :
    CStarMatrix ι τ A := CStarMatrix.ofMatrix fun i j => ∑ k, f (X i k) (Y k j)

omit [PartialOrder A] [StarOrderedRing A] in
theorem finiteBilinearProduct_reindex (f : A →ₗ[ℂ] A →ₗ[ℂ] A)
    {ι κ τ ι' κ' τ' : Type*} [Fintype κ] [Fintype κ']
    (e : ι ≃ ι') (d : κ ≃ κ') (g : τ ≃ τ')
    (X : CStarMatrix ι κ A) (Y : CStarMatrix κ τ A) :
    CStarMatrix.reindexₗ ℂ A e g (finiteBilinearProduct f X Y) =
      finiteBilinearProduct f (CStarMatrix.reindexₗ ℂ A e d X)
        (CStarMatrix.reindexₗ ℂ A d g Y) := by
  ext i j
  apply Fintype.sum_equiv d
  intro k
  change f (X (e.symm i) k) (Y k (g.symm j)) =
    f (X (e.symm i) (d.symm (d k))) (Y (d.symm (d k)) (g.symm j))
  rw [d.symm_apply_apply]

theorem HaagerupBound.finite {f : A →ₗ[ℂ] A →ₗ[ℂ] A} {c : ℝ}
    (hf : HaagerupBound f c) {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ]
    (X : CStarMatrix ι κ A) (Y : CStarMatrix κ τ A) :
    ‖finiteBilinearProduct f X Y‖ ≤ c * ‖X‖ * ‖Y‖ := by
  classical
  let e := Fintype.equivFin ι
  let d := Fintype.equivFin κ
  let g := Fintype.equivFin τ
  have h := hf _ _ _ (CStarMatrix.reindexₗ ℂ A e d X)
    (CStarMatrix.reindexₗ ℂ A d g Y)
  change ‖finiteBilinearProduct f (CStarMatrix.reindexₗ ℂ A e d X)
    (CStarMatrix.reindexₗ ℂ A d g Y)‖ ≤ _ at h
  rwa [← finiteBilinearProduct_reindex, norm_reindex_rectangular,
    norm_reindex_rectangular, norm_reindex_rectangular] at h

end

end KadisonKastler

end OAI
