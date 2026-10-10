import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteTensorFiber
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomZeroRepresentative
import OAI.Algebra.AuslanderReiten.Coordinates.TensorComparisonZeroTransport
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomCompositionSquare

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

theorem tensorFiberRhoPair_comparison (n : ℤ)
    (x : CohomologyClass (A.simpleComplete q) (tensorFiberComplete q H₁ H₂) n) :
    tensorFiberRhoPair q H₁ H₂ n x =
      (fullHomPostcomp (BalancedTensor.comparisonOut (AFrobeniusTrace k q)
          (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₁)) n
        (fullHomPostcomp (BalancedTensor.complexMap (k := k)
          (EnvelopingBimodule.mapRight (rho₁ q H₁ H₂))
          (EnvelopingBimodule.map_left_smul (rho₁ q H₁ H₂)) (A.simpleComplete q)) n x),
       fullHomPostcomp (BalancedTensor.comparisonOut (AFrobeniusTrace k q)
          (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₂)) n
        (fullHomPostcomp (BalancedTensor.complexMap (k := k)
          (EnvelopingBimodule.mapRight (rho₂ q H₁ H₂))
          (EnvelopingBimodule.map_left_smul (rho₂ q H₁ H₂)) (A.simpleComplete q)) n x)) := by
  have h₁ := fullHomPostcomp_square k n (tensorFiberOut_rho₁ q H₁ H₂) x
  have h₂ := fullHomPostcomp_square k n (tensorFiberOut_rho₂ q H₁ H₂) x
  exact (tensorFiberRhoPair_apply q H₁ H₂ n x).trans (Prod.ext h₁.symm h₂.symm)

def tensorFiberMap
    (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0) :
    A.simpleComplete q ⟶ tensorFiberComplete q H₁ H₂ :=
  fullHomZeroRepresentative ((tensorFiberFullEquiv q H₁ H₂ 0).symm g)

theorem tensorFiberMap_class
    (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0) :
    (tensorFiberFullEquiv q H₁ H₂ 0)
      (CohomologyClass.mk (Cocycle.ofHom (tensorFiberMap q H₁ H₂ g))) = g := by
  rw [tensorFiberMap, fullHomZeroRepresentative_class, LinearEquiv.apply_symm_apply]

theorem tensorFiberMap_zero_surjective
    (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0)
    (hg : ∀ z, ∃ a : k, a • g = z) :
    Function.Surjective (TriangularInduction.tensorComparison (tensorFiberMap q H₁ H₂ g) 0) :=
  TriangularInduction.tensorComparison_zero_surjective_of_equiv
    (tensorFiberMap q H₁ H₂ g) (tensorFiberFullEquiv q H₁ H₂ 0) g
    (tensorFiberMap_class q H₁ H₂ g) hg

theorem tensorFiberMap_zero_nonzero_kernel
    (hq1 : 1+q ≠ 0)
    (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0) :
    ∃ w : CohomologyClass (A.simpleComplete q) (A.simpleComplete q) 0 ×
        CohomologyClass (A.simpleComplete q) (A.simpleComplete q) 0,
      w ≠ 0 ∧ TriangularInduction.tensorComparison (tensorFiberMap q H₁ H₂ g) 0 w = 0 := by
  apply TriangularInduction.tensorComparison_zero_nonzero_kernel
  intro h
  have hh := A.fullHomZeroScalarEquiv_identity q hq1
  rw [h, map_zero] at hh
  exact zero_ne_one hh

end ArExplicit.T

end

end OAI
