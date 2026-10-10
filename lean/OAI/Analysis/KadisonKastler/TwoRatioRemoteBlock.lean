import OAI.Analysis.KadisonKastler.TwoRatioFiniteMatrix
import OAI.Analysis.KadisonKastler.PointedBlockMoments

namespace OAI

/-! # Remote copies of two-ratio matrix blocks

Both site families are shifted beyond the two specified finite stages.
The shift preserves the density parameters, so the new block has exactly
the old matrix moments and is independent of the prescribed local algebra.
-/

namespace KadisonKastler

open Generator

noncomputable section

def twoRatioRemoteSites (k n : ℕ) : List TwoRatioSite :=
  (twoRatioFiniteSites k).map (twoRatioSiteShift (max k n))

theorem twoRatioRemoteSites_nodup (k n : ℕ) : (twoRatioRemoteSites k n).Nodup :=
  (twoRatioFiniteSites_nodup k).map (twoRatioSiteShift_injective _)

def twoRatioRemoteIndex (k n : ℕ) :
    Fin (twoRatioMatrixSize k) ≃ MatrixSiteBlockIndex (twoRatioRemoteSites k n) :=
  (Fintype.equivFin (MatrixSiteBlockIndex (twoRatioFiniteSites k))).symm.trans
    (matrixSiteBlockMapEquiv (twoRatioSiteShift (max k n)) (twoRatioFiniteSites k))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

def twoRatioRemoteMatrix (k n : ℕ) :
    MatrixUnitSystem (Fin (twoRatioMatrixSize k)) (H →L[ℂ] H) :=
  (S.finiteBlock (twoRatioRemoteSites k n) (twoRatioRemoteSites_nodup k n)).reindex
    (twoRatioRemoteIndex k n)

theorem twoRatioRemoteMatrix_algebra (k n : ℕ) :
    (S.twoRatioRemoteMatrix k n).algebra =
      (S.finiteBlock (twoRatioRemoteSites k n) (twoRatioRemoteSites_nodup k n)).algebra :=
  MatrixUnitSystem.reindex_algebra _ _

theorem twoRatioRemoteMatrix_le (k n : ℕ) :
    (S.twoRatioRemoteMatrix k n).algebra ≤ M.toStarSubalgebra := by
  rw [S.twoRatioRemoteMatrix_algebra]
  exact S.finiteBlock_le _ _

theorem twoRatioRemoteMatrix_commutes (k n : ℕ)
    (i j a b : Fin (twoRatioMatrixSize k)) :
    Commute ((S.twoRatioMatrix k).entry i j) ((S.twoRatioRemoteMatrix k n).entry a b) :=
  S.finiteBlock_commuting (twoRatioSiteShift_disjoint (le_max_left k n) k) _ _ _ _

theorem twoRatioRemoteMatrix_moment (k n : ℕ) (i j : Fin (twoRatioMatrixSize k)) :
    productVectorState Ω ((S.twoRatioRemoteMatrix k n).entry i j) =
      productVectorState Ω ((S.twoRatioMatrix k).entry i j) := by
  change inner ℂ Ω (S.blockEntry (twoRatioRemoteSites k n)
    (twoRatioRemoteIndex k n i) (twoRatioRemoteIndex k n j) Ω) =
    inner ℂ Ω (S.blockEntry (twoRatioFiniteSites k)
      ((Fintype.equivFin _).symm i) ((Fintype.equivFin _).symm j) Ω)
  rw [S.blockEntry_moment _ (twoRatioRemoteSites_nodup k n),
    S.blockEntry_moment _ (twoRatioFiniteSites_nodup k)]
  exact matrixSiteBlockWeight_map _ _ _ (twoRatioSiteShift_parameter _) _ _ _

theorem twoRatioRemoteMatrix_independent (k n : ℕ) (i j : Fin (twoRatioMatrixSize k))
    (b : (S.twoRatioMatrix n).algebra) :
    productVectorState Ω ((S.twoRatioRemoteMatrix k n).entry i j * b.val) =
      productVectorState Ω ((S.twoRatioMatrix k).entry i j) * productVectorState Ω b.val := by
  have hb : b.val ∈
      (S.finiteBlock (twoRatioFiniteSites n) (twoRatioFiniteSites_nodup n)).algebra := by
    rw [← S.twoRatioMatrix_algebra n]
    exact b.property
  have h := S.disjoint_block_algebra_independent
    (twoRatioRemoteSites_nodup k n) (twoRatioFiniteSites_nodup n)
    (twoRatioSiteShift_disjoint (le_max_right k n) k).symm
    (twoRatioRemoteIndex k n i) (twoRatioRemoteIndex k n j) ⟨b.val, hb⟩
  change productVectorState Ω ((S.twoRatioRemoteMatrix k n).entry i j * b.val) =
    productVectorState Ω ((S.twoRatioRemoteMatrix k n).entry i j) *
      productVectorState Ω b.val at h
  rw [S.twoRatioRemoteMatrix_moment] at h
  exact h

end PointedMatrixSites

end

end KadisonKastler

end OAI
