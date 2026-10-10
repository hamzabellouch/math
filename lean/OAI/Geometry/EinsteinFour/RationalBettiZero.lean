import OAI.Geometry.EinsteinFour.TopologicalNumbers
import OAI.Geometry.EinsteinFour.Statement
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace OAI

/-! The degree-zero rational Betti number of an actual connected
four-manifold.  This uses singular homology, with no Hodge-theoretic or
characteristic-number premise. -/

namespace PositiveEinsteinFour.Topology

open CategoryTheory EinsteinFour

noncomputable section

universe u

/-- Augmentation identifies the singular zeroth homology with its
coefficient field on a path-connected space. -/
def rationalHomologyZeroEquiv (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] :
    rationalHomology X 0 ≃ₗ[ℚ] ULift.{u} ℚ :=
  (asIso ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℚ (ULift.{u} ℚ)))).toLinearEquiv

theorem rationalBetti_zero_of_pathConnected (X : Type u)
    [TopologicalSpace X] [PathConnectedSpace X] : rationalBetti X 0 = 1 := by
  have h := (rationalHomologyZeroEquiv X).finrank_eq
  simpa only [rationalBetti, finrank_ulift, CommSemiring.finrank_self] using h

/-- In particular, the manifold hypotheses in the classification problem
give the actual zeroth Betti number. Compactness and curvature are not needed. -/
theorem rationalBetti_zero_of_connected_manifold (M : Type u)
    [TopologicalSpace M] [ChartedSpace FourSpace M] [ConnectedSpace M] :
    rationalBetti M 0 = 1 := by
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace FourSpace M
  let : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  exact rationalBetti_zero_of_pathConnected M

end
end PositiveEinsteinFour.Topology

end OAI
