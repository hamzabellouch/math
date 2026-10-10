import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteTensorFiber

namespace OAI

noncomputable section
open CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)

def tensorFiberRhoEquiv (n : ℤ) (h : Function.Bijective (fiberFullRhoPair q H₁ H₂ n)) :
    CohomologyClass (A.simpleComplete q) (tensorFiberComplete q H₁ H₂) n ≃ₗ[k]
      (CohomologyClass (A.simpleComplete q) (A.simpleComplete q) n ×
        CohomologyClass (A.simpleComplete q) (A.simpleComplete q) n) :=
  (tensorFiberFullEquiv q H₁ H₂ n).trans
    (LinearEquiv.ofBijective (fiberFullRhoPair q H₁ H₂ n) h)

theorem tensorFiberRhoEquiv_apply (n : ℤ)
    (h : Function.Bijective (fiberFullRhoPair q H₁ H₂ n))
    (x : CohomologyClass (A.simpleComplete q) (tensorFiberComplete q H₁ H₂) n) :
    tensorFiberRhoEquiv q H₁ H₂ n h x = tensorFiberRhoPair q H₁ H₂ n x := rfl

end ArExplicit.T

end

end OAI
