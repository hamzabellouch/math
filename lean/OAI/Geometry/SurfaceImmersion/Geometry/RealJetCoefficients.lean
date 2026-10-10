import OAI.Geometry.SurfaceImmersion.Correction.PolynomialConnectionBounds
import OAI.Geometry.SurfaceImmersion.Correction.UniformRealModeCoefficients

namespace OAI

/-! Real formulas for the reconstruction coefficients at an actual real
surface jet; complexification preserves every coefficient exactly. -/
noncomputable section
open scoped Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes

def realTangentDualX (X Y : RVec 4) : RVec 4 :=
  ((Y ⬝ᵥ Y)/NormalFrame.gramDet X Y) • X+(-(X ⬝ᵥ Y)/NormalFrame.gramDet X Y) • Y

def realTangentDualY (X Y : RVec 4) : RVec 4 :=
  (-(X ⬝ᵥ Y)/NormalFrame.gramDet X Y) • X+((X ⬝ᵥ X)/NormalFrame.gramDet X Y) • Y

def realJetNormal (J : RealTwoJet) (i : Fin 5) := realNormalPart (J 0) (J 1) (J i)

def realScalarCoefficients (J : RealTwoJet) : Fin 8 → ℝ :=
  ![realConnectionX (J 0) (J 1) (J 2),realConnectionY (J 0) (J 1) (J 2),
    realConnectionX (J 0) (J 1) (J 3),realConnectionY (J 0) (J 1) (J 3),
    realConnectionX (J 0) (J 1) (J 4),realConnectionY (J 0) (J 1) (J 4),
    (realJetNormal J 2 ⬝ᵥ realJetNormal J 4)/(realJetNormal J 4 ⬝ᵥ realJetNormal J 4),
    (realJetNormal J 3 ⬝ᵥ realJetNormal J 4)/(realJetNormal J 4 ⬝ᵥ realJetNormal J 4)]

def realVectorCoefficients (J : RealTwoJet) : Fin 5 → RVec 4 :=
  ![realJetNormal J 2,realJetNormal J 3,realTangentDualX (J 0) (J 1),
    realTangentDualY (J 0) (J 1),
    (realJetNormal J 4 ⬝ᵥ realJetNormal J 4)⁻¹ • realJetNormal J 4]

lemma scalarCoefficients_complexify (J : RealTwoJet) (i : Fin 8) :
    LowJet.scalarCoefficients (complexifyJetCLM J) i = (realScalarCoefficients J i : ℂ) := by
  change LowJet.scalarCoefficients (fun k => complexify (J k)) i = _
  fin_cases i <;>
    simp [LowJet.scalarCoefficients,realScalarCoefficients,realConnectionX,
      realConnectionY,liftX,liftY,complexify_dot,complexify_gram,
      ← complexify_normalPart,realJetNormal]

lemma vectorCoefficients_complexify (J : RealTwoJet) (i : Fin 5) (a : Fin 4) :
    LowJet.vectorCoefficients (complexifyJetCLM J) i a = (realVectorCoefficients J i a : ℂ) := by
  change LowJet.vectorCoefficients (fun k => complexify (J k)) i a = _
  fin_cases i <;>
    simp [LowJet.vectorCoefficients,realVectorCoefficients,
      realTangentDualX,realTangentDualY,tangentLift,liftX,liftY,complexify_dot,complexify_gram,
      ← complexify_normalPart,realJetNormal]

end ClosedSurfaceR4.RealModes

end

end OAI
