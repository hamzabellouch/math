import OAI.Algebra.AuslanderReiten.Coordinates.FiniteTensorComparison

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.FiniteLeftModule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (X : FiniteLeftModule k R)
variable (M N : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))
variable [Module.Finite R (EnvelopingBimodule k R M.carrier)]
  [Module.Projective R (EnvelopingBimodule k R M.carrier)]
  [Module.Finite Rᵐᵒᵖ (EnvelopingBimodule k R M.carrier)]
  [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R M.carrier)]
variable [Module.Finite R (EnvelopingBimodule k R N.carrier)]
  [Module.Projective R (EnvelopingBimodule k R N.carrier)]
  [Module.Finite Rᵐᵒᵖ (EnvelopingBimodule k R N.carrier)]
  [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R N.carrier)]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

theorem evaluatedResolutionOut_fullHom (f : M.carrier ⟶ N.carrier)
    (L : FiniteLeftModule k R) (e : (evaluated X N).carrier ≃ₗ[R] L.carrier)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : CohomologyClass K (BalancedTensor.completeTensor
      (F := EnvelopingBimodule k R M.carrier) τ X) n) :
    fullHomPostcomp (BalancedTensor.comparisonOut τ X L e) n
      (fullHomPostcomp (BalancedTensor.complexMap (k := k)
        (EnvelopingBimodule.mapRight f) (EnvelopingBimodule.map_left_smul f)
        (X.completeCochain τ)) n x) =
    fullHomPostcomp (resolutionMap τ (e.toLinearMap.comp (evaluationMap X f.hom))) n
      (fullHomPostcomp (evaluatedResolutionOut τ X M) n x) := by
  rw [fullHomPostcomp_comp, fullHomPostcomp_comp]
  exact fullHomPostcomp_congr k n (evaluatedResolutionOut_natural τ X M N f L e) x

end ArExplicit.FiniteLeftModule

end

end OAI
