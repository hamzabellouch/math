import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowDeterminant

namespace OAI

/-! Coordinates of the actual spatial derivative in the standard orthonormal
basis, preserving its determinant and identifying the divergence with trace. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def flowMatrix (L : Position →L[ℝ] Position) : Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis L.toLinearMap

def flowCoordinate (a : Fin 3) : Position →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) a

theorem flowMatrix_apply (L : Position →L[ℝ] Position) (a b : Fin 3) :
    flowMatrix L a b = L (NeutralAtom.axis b) a := by
  simp only [flowMatrix,LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply,NeutralAtom.axis,ContinuousLinearMap.coe_coe]

theorem flowMatrix_comp (A B : Position →L[ℝ] Position) :
    flowMatrix (A.comp B) = flowMatrix A * flowMatrix B := by
  exact LinearMap.toMatrix_comp (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    A.toLinearMap B.toLinearMap

theorem flowMatrix_det (L : Position →L[ℝ] Position) :
    (flowMatrix L).det = L.det :=
  LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis L.toLinearMap

theorem flowMatrix_trace (v : Position → Position) (x : Position)
    (hv : DifferentiableAt ℝ v x) :
    (flowMatrix (fderiv ℝ v x)).trace = fieldDivergence v x := by
  simp only [Matrix.trace,Matrix.diag,fieldDivergence]
  apply Finset.sum_congr rfl
  intro a _
  rw [flowMatrix_apply]
  have hd := (flowCoordinate a).hasFDerivAt.comp x hv.hasFDerivAt
  change fderiv ℝ v x (NeutralAtom.axis a) a =
    fderiv ℝ ((flowCoordinate a) ∘ v) x (NeutralAtom.axis a)
  rw [hd.fderiv]
  rfl

end ContinuumCoulomb

end

end OAI
