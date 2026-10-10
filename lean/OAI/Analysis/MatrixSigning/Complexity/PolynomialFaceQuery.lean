import Mathlib
import OAI.Analysis.MatrixSigning.Realization.FaceQueryRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialPotential
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFaceBasics

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def queryScanCount (d : ℕ) (nu err : ℚ) : ℕ :=
  (RationalSDP.optimizeFuel (err/4) 100+1)*RationalSDP.searchFuel (RationalSDP.valueDimension d)
    (RationalSDP.nearRadius (err/4) (RationalSDP.valueLipschitz d (nu/d))
      (RationalSDP.valueOuterRadius d (nu/d)) (RationalSDP.valueInnerRadius d))
    (RationalSDP.valueOuterRadius d (nu/d))
lemma potential_scanCount (p : PotentialParams) : p.scanCount=queryScanCount p.d p.nu p.error := by
  rfl
def FaceParams.queryCount (p : FaceParams) (err : ℚ) : ℕ := queryScanCount p.d p.nu err
def FaceParams.stencilCount (p : FaceParams) := p.queryCount p.schedule.stencilError
def FaceParams.scoreCount (p : FaceParams) := p.queryCount p.schedule.selectionError

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_faceQuery (a : ι → FacePoint×ℚ)
    (ha : IsPoly L (fun i => (prodCode facePointCode ratCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).1.p.queryCount (a i).2)) : RunsPoly L faceQuery a := by
  unfold faceQuery
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  apply runsPoly_potentialQuery _ hw
  simpa only [potential_scanCount,FacePoint.potential,FaceParams.queryCount] using hn
lemma runsPoly_faceStencil (a : ι → FacePoint)
    (ha : IsPoly L (fun i => (facePointCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).p.stencilCount)) : RunsPoly L faceStencil a := by
  unfold faceStencil
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  apply runsPoly_faceQuery _ hw
  exact hn
lemma runsPoly_faceScore (a : ι → FacePoint)
    (ha : IsPoly L (fun i => (facePointCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).p.scoreCount)) : RunsPoly L faceScore a := by
  unfold faceScore
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  apply runsPoly_faceQuery _ hw
  exact hn
end CurrentKS.Realization

end

end OAI
