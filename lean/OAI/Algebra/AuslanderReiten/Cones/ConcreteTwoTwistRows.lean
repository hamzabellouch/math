import OAI.Algebra.AuslanderReiten.Modules.ATwistedCompleteAction
import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteTensorFiberProjection
import OAI.Algebra.AuslanderReiten.Coordinates.TensorComparisonProjectedRow

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.A k q))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (hp : Resolution.NoPositivePowerOne q)
variable (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0)
variable (hg : fiberFullRhoPair q H₁ H₂ 0 g =
  (CompleteComparison.fullHomIdentity (A.simpleComplete q),
    CompleteComparison.fullHomIdentity (A.simpleComplete q)))
include hq hq1 hp hg

theorem tensorFiberComparison_first (m : ℕ) (hm : 0 < m)
    (x : CohomologyClass (A.simpleComplete q) (A.simpleComplete q) ((3*m : ℕ) : ℤ) ×
      CohomologyClass (A.simpleComplete q) (A.simpleComplete q) ((3*m : ℕ) : ℤ)) :
    fullHomPostcomp (completeTwistOut q H₁) _
      (fullHomPostcomp (tensorRho₁ q H₁ H₂) _
        (TriangularInduction.tensorComparison (tensorFiberMap q H₁ H₂ g) _ x)) =
      (((H₁⁻¹ : kˣ) : k)^m) • x.1 + x.2 :=
  TriangularInduction.tensorComparison_projected_row
    (EnvelopingBimodule.mapRight (rho₁ q H₁ H₂))
    (EnvelopingBimodule.map_left_smul (rho₁ q H₁ H₂))
    (tensorFiberMap q H₁ H₂ g) (completeTwistIn q H₁) (completeTwistOut q H₁)
    ((tensorFiberMap_rho₁_inverse q H₁ H₂ g hg).trans (completeTwistIn_quotient q H₁).symm)
    (completeTwist_inverse q H₁) _ _ (completeTwist_scalar q H₁ hq hq1 hp m hm) x

theorem tensorFiberComparison_second (m : ℕ) (hm : 0 < m)
    (x : CohomologyClass (A.simpleComplete q) (A.simpleComplete q) ((3*m : ℕ) : ℤ) ×
      CohomologyClass (A.simpleComplete q) (A.simpleComplete q) ((3*m : ℕ) : ℤ)) :
    fullHomPostcomp (completeTwistOut q H₂) _
      (fullHomPostcomp (tensorRho₂ q H₁ H₂) _
        (TriangularInduction.tensorComparison (tensorFiberMap q H₁ H₂ g) _ x)) =
      (((H₂⁻¹ : kˣ) : k)^m) • x.1 + x.2 :=
  TriangularInduction.tensorComparison_projected_row
    (EnvelopingBimodule.mapRight (rho₂ q H₁ H₂))
    (EnvelopingBimodule.map_left_smul (rho₂ q H₁ H₂))
    (tensorFiberMap q H₁ H₂ g) (completeTwistIn q H₂) (completeTwistOut q H₂)
    ((tensorFiberMap_rho₂_inverse q H₁ H₂ g hg).trans (completeTwistIn_quotient q H₂).symm)
    (completeTwist_inverse q H₂) _ _ (completeTwist_scalar q H₂ hq hq1 hp m hm) x

theorem tensorFiberComparison_rows (m : ℕ) (hm : 0 < m)
    (x : CohomologyClass (A.simpleComplete q) (A.simpleComplete q) ((3*m : ℕ) : ℤ) ×
      CohomologyClass (A.simpleComplete q) (A.simpleComplete q) ((3*m : ℕ) : ℤ)) :
    tensorFiberRhoPair q H₁ H₂ _
      (TriangularInduction.tensorComparison (tensorFiberMap q H₁ H₂ g) _ x) =
        twoTwistLinear (((H₁⁻¹ : kˣ) : k)^m) (((H₂⁻¹ : kˣ) : k)^m) x := by
  refine (tensorFiberRhoPair_comparison q H₁ H₂ _ _).trans (Prod.ext ?_ ?_)
  · exact (fullHomPostcomp_congr k _
      ((BalancedTensor.comparisonOut_quotient (AFrobeniusTrace k q)
        (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₁)).trans
          (completeTwistOut_quotient q H₁).symm) _).trans
      (tensorFiberComparison_first q H₁ H₂ hq hq1 hp g hg m hm x)
  · exact (fullHomPostcomp_congr k _
      ((BalancedTensor.comparisonOut_quotient (AFrobeniusTrace k q)
        (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₂)).trans
          (completeTwistOut_quotient q H₂).symm) _).trans
      (tensorFiberComparison_second q H₁ H₂ hq hq1 hp g hg m hm x)

end ArExplicit.T

end

end OAI
