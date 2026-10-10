import OAI.Geometry.EinsteinFour.TraceDecomposition
import OAI.Geometry.EinsteinFour.HighestProjection

namespace OAI

/-! The local weighted square from the original Hessian identities. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- The concrete trace-free remainder of the covariant Weyl Hessian. -/
def hessianRemainder (X : Hessian) (t : Fin 3 → ℝ) : Hessian :=
  X - traceComponent (diagonalLaplacianBlock t)

/-- The nonnegative local square follows from the classical local tensor
identities. The weight tensor is unsymmetrized and its highest projection
is the constructed Euclidean orthogonal projection. -/
theorem local_weighted_hessian_square
    (X : Hessian) (t u : Fin 3 → ℝ) (a : Vec) (Z : Tensor)
    (ht : ∑ s, t s = 0)
    (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (htrace : hessianTrace X = diagonalLaplacianBlock t)
    (hbianchi : ∀ i r, divergence X i r = 0)
    (hcomm : ∀ i j b c, X i j b c - X j i b c =
      (1 / 2) * ∑ s, (1 + t s) * quaternionMatrix s i j *
        matrixAction s (Matrix.diagonal t) b c)
    (x y m : ℝ) (hm : 0 < m)
    (htx : ∀ s, -x ≤ t s) (huy : ∀ s, -y ≤ u s) (hxy : x + y ≤ 2) :
    0 ≤ (m / 6) * curvaturePairing t u (hessianRemainder X t) (hessianRemainder X t) +
      curvaturePairing t u (hessianRemainder X t) (weightTensor a Z) / 6 +
      curvaturePairing t u (highestProjection (weightTensor a Z))
        (highestProjection (weightTensor a Z)) / (24 * m) := by
  have hY : condition (hessianRemainder X t) :=
    trace_subtracted_condition X t ht hmatrix htrace hbianchi hcomm
  exact weighted_highestProjection_square (hessianRemainder X t) (weightTensor a Z)
    hY t u x y m hm htx huy hxy

end
end PositiveEinsteinFour.HighestHessian

end OAI
