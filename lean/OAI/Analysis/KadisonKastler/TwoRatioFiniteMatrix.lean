import OAI.Analysis.KadisonKastler.TwoRatioFiniteSites
import OAI.Analysis.KadisonKastler.PointedFiniteBlock

namespace OAI

/-! # The increasing full matrix algebras of the two-ratio product -/

namespace KadisonKastler

open Generator

noncomputable section

def twoRatioMatrixSize (n : ℕ) : ℕ :=
  Fintype.card (MatrixSiteBlockIndex (twoRatioFiniteSites n))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

def twoRatioMatrix (n : ℕ) : MatrixUnitSystem (Fin (twoRatioMatrixSize n)) (H →L[ℂ] H) :=
  (S.finiteBlock (twoRatioFiniteSites n) (twoRatioFiniteSites_nodup n)).reindex
    (Fintype.equivFin (MatrixSiteBlockIndex (twoRatioFiniteSites n))).symm

theorem twoRatioMatrix_algebra (n : ℕ) :
    (S.twoRatioMatrix n).algebra =
      (S.finiteBlock (twoRatioFiniteSites n) (twoRatioFiniteSites_nodup n)).algebra :=
  MatrixUnitSystem.reindex_algebra _ _

theorem twoRatioMatrix_increasing : Monotone (fun n => (S.twoRatioMatrix n).algebra) := by
  intro n m h
  change (S.twoRatioMatrix n).algebra ≤ (S.twoRatioMatrix m).algebra
  rw [S.twoRatioMatrix_algebra, S.twoRatioMatrix_algebra]
  exact S.finiteBlock_mono _ _ (twoRatioFiniteSites_mono h)

theorem twoRatioMatrix_le (n : ℕ) : (S.twoRatioMatrix n).algebra ≤ M.toStarSubalgebra := by
  rw [S.twoRatioMatrix_algebra]
  exact S.finiteBlock_le _ _

theorem twoRatioMatrix_generates :
    generatedVonNeumannAlgebra (⨆ n, (S.twoRatioMatrix n).algebra) = M := by
  apply le_antisymm
  · exact generatedVonNeumannAlgebra_le_of_le _ M (iSup_le S.twoRatioMatrix_le)
  · calc
      M = generatedVonNeumannAlgebra (⨆ i, (S.site i).algebra) := S.generates
      _ ≤ generatedVonNeumannAlgebra (⨆ n, (S.twoRatioMatrix n).algebra) := by
        apply generatedVonNeumannAlgebra_le_of_le _ _
        apply iSup_le
        intro i x hx
        obtain ⟨n, hn⟩ := twoRatioFiniteSites_exhausts i
        have hm : x ∈ (S.twoRatioMatrix n).algebra := by
          rw [S.twoRatioMatrix_algebra]
          exact S.site_le_finiteBlock _ _ i hn hx
        have hle : (S.twoRatioMatrix n).algebra ≤
            ⨆ n, (S.twoRatioMatrix n).algebra :=
          le_iSup (fun n : ℕ => (S.twoRatioMatrix n).algebra) n
        exact subset_generatedVonNeumannAlgebra _ (hle hm)

theorem twoRatioMatrix_local_cyclic : DenseRange
    (fun p : Σ n, (S.twoRatioMatrix n).algebra => (p.2 : H →L[ℂ] H) Ω) := by
  classical
  apply Metric.denseRange_iff.mpr
  intro x ε hε
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp S.cyclic x (ε / 2) (by positivity)
  change dist x (a.val Ω) < ε / 2 at ha
  have hax : dist (a.val Ω) x < ε / 2 := by
    simpa only [dist_comm] using ha
  let A : StarSubalgebra ℂ (H →L[ℂ] H) := ⨆ n, (S.twoRatioMatrix n).algebra
  have ham : a.val ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
    rw [← generatedVonNeumannAlgebra_coe, S.twoRatioMatrix_generates]
    exact a.property
  obtain ⟨b, hb⟩ := Generator.bicommutant_finite_strong_approximation A a.val ham
    {Ω} (ε / 2) (by positivity)
  have hbm : b.val ∈ ⋃ n, ((S.twoRatioMatrix n).algebra : Set (H →L[ℂ] H)) := by
    rw [← StarSubalgebra.coe_iSup_of_directed S.twoRatioMatrix_increasing.directed_le]
    exact b.property
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hbm
  refine ⟨⟨n, ⟨b.val, hn⟩⟩, ?_⟩
  have hbΩ : dist (b.val Ω) (a.val Ω) < ε / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hb Ω (Finset.mem_singleton_self _)
  rw [dist_comm]
  change dist (b.val Ω) x < ε
  calc
    dist (b.val Ω) x ≤ dist (b.val Ω) (a.val Ω) + dist (a.val Ω) x := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hbΩ hax
    _ = ε := by ring

end PointedMatrixSites

end

end KadisonKastler

end OAI
