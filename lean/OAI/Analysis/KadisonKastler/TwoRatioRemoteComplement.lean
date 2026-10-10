import OAI.Analysis.KadisonKastler.TwoRatioRemoteBlock

namespace OAI

/-! # Finite complements for remote product blocks -/

namespace KadisonKastler

open Generator

noncomputable section

def twoRatioComplementSites (k n m : ℕ) : List TwoRatioSite := by
  classical
  exact (twoRatioFiniteSites m).filter fun i =>
    decide (i ∉ twoRatioFiniteSites k ∧ i ∉ twoRatioRemoteSites k n)

@[simp] theorem mem_twoRatioComplementSites (k n m : ℕ) (i : TwoRatioSite) :
    i ∈ twoRatioComplementSites k n m ↔ i ∈ twoRatioFiniteSites m ∧
      i ∉ twoRatioFiniteSites k ∧ i ∉ twoRatioRemoteSites k n := by
  simp [twoRatioComplementSites]

theorem twoRatioComplementSites_nodup (k n m : ℕ) :
    (twoRatioComplementSites k n m).Nodup :=
  (twoRatioFiniteSites_nodup m).filter _

theorem twoRatioComplementSites_disjoint (k n m : ℕ) :
    List.Disjoint (twoRatioFiniteSites k) (twoRatioComplementSites k n m) ∧
      List.Disjoint (twoRatioRemoteSites k n) (twoRatioComplementSites k n m) := by
  constructor
  · exact List.disjoint_left.mpr fun i hi hj =>
      ((mem_twoRatioComplementSites k n m i).mp hj).2.1 hi
  · exact List.disjoint_left.mpr fun i hi hj =>
      ((mem_twoRatioComplementSites k n m i).mp hj).2.2 hi

def twoRatioComplementSize (k n m : ℕ) : ℕ :=
  Fintype.card (MatrixSiteBlockIndex (twoRatioComplementSites k n m))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

def twoRatioComplementMatrix (k n m : ℕ) :
    MatrixUnitSystem (Fin (twoRatioComplementSize k n m)) (H →L[ℂ] H) :=
  (S.finiteBlock (twoRatioComplementSites k n m)
    (twoRatioComplementSites_nodup k n m)).reindex (Fintype.equivFin _).symm

theorem twoRatioComplementMatrix_algebra (k n m : ℕ) :
    (S.twoRatioComplementMatrix k n m).algebra =
      (S.finiteBlock (twoRatioComplementSites k n m)
        (twoRatioComplementSites_nodup k n m)).algebra :=
  MatrixUnitSystem.reindex_algebra _ _

theorem twoRatioComplementMatrix_commutes (k n m : ℕ)
    (i j : Fin (twoRatioMatrixSize k) × Fin (twoRatioMatrixSize k))
    (a b : Fin (twoRatioComplementSize k n m)) :
    Commute (((S.twoRatioMatrix k).product (S.twoRatioRemoteMatrix k n)
      (S.twoRatioRemoteMatrix_commutes k n)).entry i j)
        ((S.twoRatioComplementMatrix k n m).entry a b) := by
  apply Commute.mul_left
  · exact S.finiteBlock_commuting (twoRatioComplementSites_disjoint k n m).1 _ _ _ _
  · exact S.finiteBlock_commuting (twoRatioComplementSites_disjoint k n m).2 _ _ _ _

theorem twoRatioComplementMatrix_contains_stage (k n m : ℕ) :
    (S.twoRatioMatrix m).algebra ≤
      (((S.twoRatioMatrix k).product (S.twoRatioRemoteMatrix k n)
        (S.twoRatioRemoteMatrix_commutes k n)).product
          (S.twoRatioComplementMatrix k n m)
            (S.twoRatioComplementMatrix_commutes k n m)).algebra := by
  rw [MatrixUnitSystem.product_algebra_eq_sup, MatrixUnitSystem.product_algebra_eq_sup,
    S.twoRatioMatrix_algebra m]
  apply S.finiteBlock_le_of_sites_le
  intro i hi
  by_cases hk : i ∈ twoRatioFiniteSites k
  · apply le_trans (S.site_le_finiteBlock _ _ i hk)
    rw [← S.twoRatioMatrix_algebra k]
    exact le_sup_left.trans le_sup_left
  · by_cases hn : i ∈ twoRatioRemoteSites k n
    · apply le_trans (S.site_le_finiteBlock _ _ i hn)
      rw [← S.twoRatioRemoteMatrix_algebra k n]
      exact le_sup_right.trans le_sup_left
    · have hm : i ∈ twoRatioComplementSites k n m :=
        (mem_twoRatioComplementSites k n m i).mpr ⟨hi, hk, hn⟩
      apply le_trans (S.site_le_finiteBlock _ _ i hm)
      rw [← S.twoRatioComplementMatrix_algebra k n m]
      exact le_sup_right

theorem twoRatioComplementMatrix_moment (k n m : ℕ)
    (i j a b : Fin (twoRatioMatrixSize k))
    (c d : Fin (twoRatioComplementSize k n m)) :
    productVectorState Ω
      ((((S.twoRatioMatrix k).product (S.twoRatioRemoteMatrix k n)
        (S.twoRatioRemoteMatrix_commutes k n)).entry (i, j) (a, b)) *
          (S.twoRatioComplementMatrix k n m).entry c d) =
      productVectorState Ω ((S.twoRatioMatrix k).entry i a) *
        productVectorState Ω ((S.twoRatioMatrix k).entry j b) *
          productVectorState Ω ((S.twoRatioComplementMatrix k n m).entry c d) := by
  have h := S.disjoint_three_blockEntry_moment
    (twoRatioFiniteSites_nodup k) (twoRatioRemoteSites_nodup k n)
    (twoRatioComplementSites_nodup k n m)
    (twoRatioSiteShift_disjoint (le_max_left k n) k)
    (twoRatioComplementSites_disjoint k n m).1
    (twoRatioComplementSites_disjoint k n m).2
    ((Fintype.equivFin _).symm i) ((Fintype.equivFin _).symm a)
    (twoRatioRemoteIndex k n j) (twoRatioRemoteIndex k n b)
    ((Fintype.equivFin _).symm c) ((Fintype.equivFin _).symm d)
  rw [← S.blockEntry_moment _ (twoRatioFiniteSites_nodup k),
    ← S.blockEntry_moment _ (twoRatioRemoteSites_nodup k n),
    ← S.blockEntry_moment _ (twoRatioComplementSites_nodup k n m)] at h
  change productVectorState Ω
      ((((S.twoRatioMatrix k).product (S.twoRatioRemoteMatrix k n)
        (S.twoRatioRemoteMatrix_commutes k n)).entry (i, j) (a, b)) *
          (S.twoRatioComplementMatrix k n m).entry c d) =
      productVectorState Ω ((S.twoRatioMatrix k).entry i a) *
        productVectorState Ω ((S.twoRatioRemoteMatrix k n).entry j b) *
          productVectorState Ω ((S.twoRatioComplementMatrix k n m).entry c d) at h
  rw [S.twoRatioRemoteMatrix_moment] at h
  exact h

end PointedMatrixSites

end

end KadisonKastler

end OAI
