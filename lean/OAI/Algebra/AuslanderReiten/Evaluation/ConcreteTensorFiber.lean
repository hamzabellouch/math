import OAI.Algebra.AuslanderReiten.Fibers.ExplicitBimoduleProjective
import OAI.Algebra.AuslanderReiten.Tensor.TwistedEnvelopingProjective
import OAI.Algebra.AuslanderReiten.Coordinates.FiniteTensorComparisonEquiv
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomCompositionLinear
import OAI.Algebra.AuslanderReiten.Fibers.FiberFullHomCoordinates

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

local instance : Module.Finite (A k q)
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) :=
  by
    simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
      using (explicitBimodule_left q H₁ H₂).1
local instance : Module.Projective (A k q)
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) :=
  by
    simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
      using (explicitBimodule_left q H₁ H₂).2
local instance : Module.Finite (A k q)ᵐᵒᵖ
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) :=
  by
    simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
      using (explicitBimodule_right q H₁ H₂).1
local instance : Module.Projective (A k q)ᵐᵒᵖ
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) :=
  by
    simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
      using (explicitBimodule_right q H₁ H₂).2

abbrev tensorFiberComplete := BalancedTensor.completeTensor
  (F := EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier)
    (AFrobeniusTrace k q) (A.simpleFiniteModule q)

abbrev tensorFiberOut := FiniteLeftModule.evaluatedResolutionOut
  (AFrobeniusTrace k q) (A.simpleFiniteModule q) (finiteFiber q H₁ H₂)

def tensorFiberFullEquiv (n : ℤ) :
    CohomologyClass (A.simpleComplete q) (tensorFiberComplete q H₁ H₂) n ≃ₗ[k]
      CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) n :=
  FiniteLeftModule.evaluatedResolutionFullEquiv (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (finiteFiber q H₁ H₂) (A.simpleComplete q) n

theorem tensorFiberFullEquiv_apply (n : ℤ)
    (x : CohomologyClass (A.simpleComplete q) (tensorFiberComplete q H₁ H₂) n) :
    tensorFiberFullEquiv q H₁ H₂ n x = fullHomPostcomp (tensorFiberOut q H₁ H₂) n x :=
  FiniteLeftModule.evaluatedResolutionFullEquiv_apply (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (finiteFiber q H₁ H₂) (A.simpleComplete q) n x

def tensorFiberRhoPair (n : ℤ) :
    CohomologyClass (A.simpleComplete q) (tensorFiberComplete q H₁ H₂) n →ₗ[k]
      (CohomologyClass (A.simpleComplete q) (A.simpleComplete q) n ×
        CohomologyClass (A.simpleComplete q) (A.simpleComplete q) n) :=
  (fiberFullRhoPair q H₁ H₂ n).comp (tensorFiberFullEquiv q H₁ H₂ n).toLinearMap

theorem tensorFiberOut_rho₁ :
    (HomotopyCategory.quotient _ _).map
      (BalancedTensor.complexMap (k := k) (EnvelopingBimodule.mapRight (rho₁ q H₁ H₂))
        (EnvelopingBimodule.map_left_smul (rho₁ q H₁ H₂)) (A.simpleComplete q) ≫
          BalancedTensor.comparisonOut (AFrobeniusTrace k q) (A.simpleFiniteModule q)
            (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₁)) =
    (HomotopyCategory.quotient _ _).map
      (tensorFiberOut q H₁ H₂ ≫
        FiniteLeftModule.resolutionMap (AFrobeniusTrace k q) (evaluatedRho₁ q H₁ H₂)) :=
  FiniteLeftModule.evaluatedResolutionOut_natural (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (finiteFiber q H₁ H₂)
    (twistedFiniteModule (sourceTwist q H₁)) (rho₁ q H₁ H₂)
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₁)

theorem tensorFiberOut_rho₂ :
    (HomotopyCategory.quotient _ _).map
      (BalancedTensor.complexMap (k := k) (EnvelopingBimodule.mapRight (rho₂ q H₁ H₂))
        (EnvelopingBimodule.map_left_smul (rho₂ q H₁ H₂)) (A.simpleComplete q) ≫
          BalancedTensor.comparisonOut (AFrobeniusTrace k q) (A.simpleFiniteModule q)
            (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₂)) =
    (HomotopyCategory.quotient _ _).map
      (tensorFiberOut q H₁ H₂ ≫
        FiniteLeftModule.resolutionMap (AFrobeniusTrace k q) (evaluatedRho₂ q H₁ H₂)) :=
  FiniteLeftModule.evaluatedResolutionOut_natural (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (finiteFiber q H₁ H₂)
    (twistedFiniteModule (sourceTwist q H₂)) (rho₂ q H₁ H₂)
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₂)

theorem tensorFiberRhoPair_apply (n : ℤ)
    (x : CohomologyClass (A.simpleComplete q) (tensorFiberComplete q H₁ H₂) n) :
    tensorFiberRhoPair q H₁ H₂ n x =
      (fullHomPostcomp (FiniteLeftModule.resolutionMap (AFrobeniusTrace k q)
          (evaluatedRho₁ q H₁ H₂)) n (fullHomPostcomp (tensorFiberOut q H₁ H₂) n x),
       fullHomPostcomp (FiniteLeftModule.resolutionMap (AFrobeniusTrace k q)
          (evaluatedRho₂ q H₁ H₂)) n (fullHomPostcomp (tensorFiberOut q H₁ H₂) n x)) :=
  by
    simpa only [tensorFiberRhoPair, LinearMap.comp_apply, LinearEquiv.coe_coe,
      tensorFiberFullEquiv_apply] using
      (fiberFullRhoPair_apply q H₁ H₂ n (tensorFiberFullEquiv q H₁ H₂ n x))

end ArExplicit.T

end

end OAI
