import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Hessian
import OAI.Analysis.MatrixSigning.Matrices.FDerivTightPart
import OAI.Analysis.MatrixSigning.Optimization.Variables

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

abbrev Vars (d : ℕ) := CurrentKS.KKT.Variables (PairHilbert d)

local instance : NormedAddCommGroup (Vars d) := inferInstance
local instance : NormedSpace ℝ (Vars d) := inferInstance

def identityPair (d : ℕ) : PairHilbert d := (pairEquiv d).symm (Hermitian.one,Hermitian.one)

def tCoord (d : ℕ) : Vars d →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (PairHilbert d × PairHilbert d)
def uCoord (d : ℕ) : Vars d →L[ℝ] PairHilbert d :=
  (ContinuousLinearMap.fst ℝ (PairHilbert d) (PairHilbert d)).comp
    (ContinuousLinearMap.snd ℝ ℝ (PairHilbert d × PairHilbert d))
def pCoord (d : ℕ) : Vars d →L[ℝ] PairHilbert d :=
  (ContinuousLinearMap.snd ℝ (PairHilbert d) (PairHilbert d)).comp
    (ContinuousLinearMap.snd ℝ ℝ (PairHilbert d × PairHilbert d))
def xCoord (d : ℕ) : Vars d →L[ℝ] H d := (WithLp.fstL 2 ℝ (H d) (H d)).comp (uCoord d)
def yCoord (d : ℕ) : Vars d →L[ℝ] H d := (WithLp.sndL 2 ℝ (H d) (H d)).comp (uCoord d)
def mCoord (d : ℕ) : Vars d →L[ℝ] H d := (WithLp.fstL 2 ℝ (H d) (H d)).comp (pCoord d)
def nCoord (d : ℕ) : Vars d →L[ℝ] H d := (WithLp.sndL 2 ℝ (H d) (H d)).comp (pCoord d)

def kktSystem (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Vars d) : Vars d :=
  (inner ℝ (identityPair d) (pCoord d z) - 1,
   (pairEquiv d).symm
    (tCoord d z • (Hermitian.one : H d) - invH (xCoord d z) - S - η (yCoord d z),
     tCoord d z • (Hermitian.one : H d) - invH (yCoord d z) + S - η (xCoord d z)),
   (pairEquiv d).symm
    (sandwich (invH (xCoord d z)) (mCoord d z) - η (nCoord d z) - ε • (Hermitian.one : H d),
     sandwich (invH (yCoord d z)) (nCoord d z) - η (mCoord d z) - ε • (Hermitian.one : H d)))

lemma hasFDerivAt_kktSystem (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d) :
    HasFDerivAt (kktSystem ε S η)
      (CurrentKS.KKT.jacobian (identityPair d)
        (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) η))
        (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z))) z := by
  have hr := (((innerSL ℝ (identityPair d)).hasFDerivAt.comp z (pCoord d).hasFDerivAt).sub_const 1)
  have hfx := hasFDerivAt_tightPart (tCoord d) (xCoord d) (yCoord d) S η z hX
  have hfy := hasFDerivAt_tightPart (tCoord d) (yCoord d) (xCoord d) (-S) η z hY
  have hfu := (pairEquiv d).symm.hasFDerivAt.comp z (hfx.prodMk hfy)
  have hgx := hasFDerivAt_stationaryPart (xCoord d) (mCoord d) (nCoord d) ε η z hX
  have hgy := hasFDerivAt_stationaryPart (yCoord d) (nCoord d) (mCoord d) ε η z hY
  have hgp := (pairEquiv d).symm.hasFDerivAt.comp z (hgx.prodMk hgy)
  have hf := hr.prodMk (hfu.prodMk hgp)
  simp only [sub_neg_eq_add] at hf
  convert hf using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply (pairEquiv d).injective
      apply Prod.ext
      · change sandwich (invH (xCoord d z)) (xCoord d v) - η (yCoord d v) +
          tCoord d v • (Hermitian.one : H d) =
          tCoord d v • (Hermitian.one : H d) + sandwich (invH (xCoord d z)) (xCoord d v) - η (yCoord d v)
        module
      · change sandwich (invH (yCoord d z)) (yCoord d v) - η (xCoord d v) +
          tCoord d v • (Hermitian.one : H d) =
          tCoord d v • (Hermitian.one : H d) + sandwich (invH (yCoord d z)) (yCoord d v) - η (xCoord d v)
        module
    · rfl

end
end CurrentKS.Variational

end OAI
