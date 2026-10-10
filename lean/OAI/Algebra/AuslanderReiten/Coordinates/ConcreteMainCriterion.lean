import OAI.Algebra.AuslanderReiten.Coordinates.ConcreteComparisonPositive
import OAI.Algebra.AuslanderReiten.Triangular.ConvertedTensorCriterion

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

local instance : Module.Finite (A k q)
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) := by
  simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
    using (explicitBimodule_left q H₁ H₂).1
local instance : Module.Projective (A k q)
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) := by
  simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
    using (explicitBimodule_left q H₁ H₂).2
local instance : Module.Finite (A k q)ᵐᵒᵖ
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) := by
  simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
    using (explicitBimodule_right q H₁ H₂).1
local instance : Module.Projective (A k q)ᵐᵒᵖ
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) := by
  simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
    using (explicitBimodule_right q H₁ H₂).2

variable (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0)

abbrev explicitAlgebra := ConvertedAlgebra k q
  (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier)

abbrev explicitLeftModule := ConeModule
  (TriangularInduction.crossChainMap (tensorFiberMap q H₁ H₂ g))

theorem explicit_mainConclusions (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (hp : Resolution.NoPositivePowerOne q)
    (hg : fiberFullRhoPair q H₁ H₂ 0 g =
      (CompleteComparison.fullHomIdentity (A.simpleComplete q),
        CompleteComparison.fullHomIdentity (A.simpleComplete q)))
    (hspan : ∀ z, ∃ a : k, a • g = z)
    (hrho : ∀ n : ℤ, 0 < n → Function.Bijective (fiberFullRhoPair q H₁ H₂ n))
    (hsep : ∀ m : ℕ, 0 < m → (((H₁⁻¹ : kˣ) : k)^m) ≠ (((H₂⁻¹ : kˣ) : k)^m)) :
    MainConclusions k (explicitAlgebra q H₁ H₂) (explicitLeftModule q H₁ H₂ g) := by
  apply convertedTensorCone_mainConclusions q
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier)
    (A.simpleComplete q) (tensorFiberMap q H₁ H₂ g) hq hq1
    ((A.simpleFiniteModule q).completeCochain_totallyAcyclic (AFrobeniusTrace k q))
  · intro n hn
    exact (tensorFiberComparison_positive_bijective q H₁ H₂ hq hq1 hp g hg hrho hsep n hn).1
  · intro n
    rcases n with _ | n
    · exact tensorFiberMap_zero_surjective q H₁ H₂ g hspan
    · exact (tensorFiberComparison_positive_bijective q H₁ H₂ hq hq1 hp g hg hrho hsep
        (n+1) (by omega)).2
  · exact tensorFiberMap_zero_nonzero_kernel q H₁ H₂ hq1 g

end ArExplicit.T

end

end OAI
