import OAI.Analysis.KadisonKastler.TwoRatioRemoteComplement
import OAI.Analysis.KadisonKastler.ProductMatrixStages

namespace OAI

/-! # Product matrix stages constructed from two-ratio coordinates -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

def twoRatioStages : ProductMatrixStages (H := H) where
  size := twoRatioMatrixSize
  matrix := S.twoRatioMatrix
  increasing := S.twoRatioMatrix_increasing
  vector := Ω
  unit_vector := S.unit_vector
  local_cyclic := S.twoRatioMatrix_local_cyclic
  separating := by
    rw [S.twoRatioMatrix_generates]
    exact S.separating
  remote k n := ⟨{
    copy := S.twoRatioRemoteMatrix k n
    copy_mem := by
      rw [S.twoRatioMatrix_generates]
      exact S.twoRatioRemoteMatrix_le k n
    commutes := S.twoRatioRemoteMatrix_commutes k n
    independent := S.twoRatioRemoteMatrix_independent k n
    complement := fun m => ⟨twoRatioComplementSize k n m,
      S.twoRatioComplementMatrix k n m, S.twoRatioComplementMatrix_commutes k n m,
      S.twoRatioComplementMatrix_contains_stage k n m,
      (fun i j => productVectorState Ω ((S.twoRatioComplementMatrix k n m).entry i j)),
      S.twoRatioComplementMatrix_moment k n m⟩ }⟩

theorem twoRatioStages_algebra : S.twoRatioStages.algebra = M :=
  S.twoRatioMatrix_generates

def twoRatioStages_coordinates :
    PointedMatrixSites S.twoRatioStages.algebra S.twoRatioStages.vector
      twoRatioSiteParameter := by
  change PointedMatrixSites S.twoRatioStages.algebra Ω twoRatioSiteParameter
  rw [S.twoRatioStages_algebra]
  exact S

end PointedMatrixSites

end

end KadisonKastler

end OAI
