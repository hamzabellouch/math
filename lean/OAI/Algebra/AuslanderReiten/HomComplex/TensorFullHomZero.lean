import OAI.Algebra.AuslanderReiten.HomComplex.FiniteFullHomZero
import OAI.Algebra.AuslanderReiten.Stable.TensorStableEnd
import OAI.Algebra.AuslanderReiten.Cones.ConcreteTwoConeEvaluation

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.A
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

def simpleComplete := (simpleFiniteModule q).completeCochain (AFrobeniusTrace k q)

def fullHomZeroScalarEquiv (hq1 : 1+q ≠ 0) :
    CohomologyClass (simpleComplete q) (simpleComplete q) 0 ≃ₗ[k] k :=
  (FiniteLeftModule.fullHomZeroEquiv (AFrobeniusTrace k q)
    (simpleFiniteModule q) (simpleFiniteModule q)).trans (stableEndEquiv q hq1)

@[simp]
theorem fullHomZeroScalarEquiv_identity (hq1 : 1+q ≠ 0) :
    fullHomZeroScalarEquiv q hq1 (CohomologyClass.mk (Cocycle.ofHom (𝟙 (simpleComplete q)))) = 1 := by
  change stableEndEquiv q hq1 (FiniteLeftModule.fullHomZeroEquiv (AFrobeniusTrace k q)
    (simpleFiniteModule q) (simpleFiniteModule q) _) = 1
  erw [FiniteLeftModule.fullHomZeroEquiv_identity, stableEndEquiv_identity]

end ArExplicit.A

end

end OAI
