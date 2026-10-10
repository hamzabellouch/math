import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteTensorFiberMaps
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomZeroProjection

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

abbrev tensorRho₁ := BalancedTensor.complexMap (k := k)
  (EnvelopingBimodule.mapRight (rho₁ q H₁ H₂))
  (EnvelopingBimodule.map_left_smul (rho₁ q H₁ H₂)) (A.simpleComplete q)

abbrev tensorRho₂ := BalancedTensor.complexMap (k := k)
  (EnvelopingBimodule.mapRight (rho₂ q H₁ H₂))
  (EnvelopingBimodule.map_left_smul (rho₂ q H₁ H₂)) (A.simpleComplete q)

variable (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0)

theorem tensorFiberMap_pair_image :
    tensorFiberRhoPair q H₁ H₂ 0
      (CohomologyClass.mk (Cocycle.ofHom (tensorFiberMap q H₁ H₂ g))) =
        fiberFullRhoPair q H₁ H₂ 0 g :=
  congrArg (fiberFullRhoPair q H₁ H₂ 0) (tensorFiberMap_class q H₁ H₂ g)

variable (hg : fiberFullRhoPair q H₁ H₂ 0 g =
  (CompleteComparison.fullHomIdentity (A.simpleComplete q),
    CompleteComparison.fullHomIdentity (A.simpleComplete q)))

include hg

theorem tensorFiberMap_rho₁_inverse :
    (HomotopyCategory.quotient _ _).map (tensorFiberMap q H₁ H₂ g ≫ tensorRho₁ q H₁ H₂) =
      (BalancedTensor.completeTensorIso (AFrobeniusTrace k q)
        (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₁)).inv := by
  let b := BalancedTensor.comparisonOut (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₁)
  apply fullHomZero_projection_inverse k _ b _
    (BalancedTensor.comparisonOut_quotient (AFrobeniusTrace k q)
      (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₁))
  have h := congrArg Prod.fst
    ((tensorFiberRhoPair_comparison q H₁ H₂ 0
      (CohomologyClass.mk (Cocycle.ofHom (tensorFiberMap q H₁ H₂ g)))).symm.trans
        ((tensorFiberMap_pair_image q H₁ H₂ g).trans hg))
  exact (congrArg (fullHomPostcomp b 0)
    (fullHomPostcomp_ofHom (tensorFiberMap q H₁ H₂ g) (tensorRho₁ q H₁ H₂))).symm.trans h

theorem tensorFiberMap_rho₂_inverse :
    (HomotopyCategory.quotient _ _).map (tensorFiberMap q H₁ H₂ g ≫ tensorRho₂ q H₁ H₂) =
      (BalancedTensor.completeTensorIso (AFrobeniusTrace k q)
        (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₂)).inv := by
  let b := BalancedTensor.comparisonOut (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₂)
  apply fullHomZero_projection_inverse k _ b _
    (BalancedTensor.comparisonOut_quotient (AFrobeniusTrace k q)
      (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₂))
  have h := congrArg Prod.snd
    ((tensorFiberRhoPair_comparison q H₁ H₂ 0
      (CohomologyClass.mk (Cocycle.ofHom (tensorFiberMap q H₁ H₂ g)))).symm.trans
        ((tensorFiberMap_pair_image q H₁ H₂ g).trans hg))
  exact (congrArg (fullHomPostcomp b 0)
    (fullHomPostcomp_ofHom (tensorFiberMap q H₁ H₂ g) (tensorRho₂ q H₁ H₂))).symm.trans h

end ArExplicit.T

end

end OAI
