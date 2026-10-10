import OAI.Algebra.AuslanderReiten.Triangular.ConvertedCriterion
import OAI.Algebra.AuslanderReiten.Triangular.TriangularCochain
import OAI.Algebra.AuslanderReiten.Triangular.ConvertedStructure
import OAI.Algebra.AuslanderReiten.Triangular.TriangularComparisonTransport

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CompleteComparison TriangularInduction
open CochainComplex CochainComplex.HomComplex

universe u

variable {k : Type u} [Field k] (q : k) (B : Type u)
variable [AddCommGroup B] [Module k B] [Module (A k q) B] [Module (A k q)ᵐᵒᵖ B]
variable [SMulCommClass k (A k q) B] [SMulCommClass (A k q) (A k q)ᵐᵒᵖ B]
variable [IsScalarTower k (A k q) B] [IsScalarTower k (A k q)ᵐᵒᵖ B]
variable [SMulCommClass k (A k q)ᵐᵒᵖ B]
variable [Module.Finite k B]
variable [Module.Finite (A k q) B] [Module.Projective (A k q) B]
variable [Module.Finite (A k q)ᵐᵒᵖ B] [Module.Projective (A k q)ᵐᵒᵖ B]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : CochainComplex (ModuleCat.{u} (A k q)) ℤ)
variable (v : P ⟶ tensorCochain (k := k) (F := B) P)

theorem convertedTensorCone_mainConclusions (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (hP : TotallyAcyclicCochain P)
    (hinj : ∀ n : ℕ, 0 < n → Function.Injective (tensorComparison v (n : ℤ)))
    (hsurj : ∀ n : ℕ, Function.Surjective (tensorComparison v (n : ℤ)))
    (hker : ∃ w : CohomologyClass P P 0 × CohomologyClass P P 0,
      w ≠ 0 ∧ tensorComparison v 0 w = 0) :
    MainConclusions k (ConvertedAlgebra k q B) (ConeModule (crossChainMap v)) := by
  apply convertedCone_mainConclusions q B P (crossChainMap v) hq hq1 hP
  · intro n hn
    exact coneComparison_injective_of_tensor v (n : ℤ) (hinj n hn)
  · intro n
    exact coneComparison_surjective_of_tensor v (n : ℤ) (hsurj n)
  · exact coneComparison_nonzero_kernel_of_tensor v 0 hker

end ArExplicit

end

end OAI
