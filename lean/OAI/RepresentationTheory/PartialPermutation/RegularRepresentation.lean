import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Model

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation
noncomputable section
variable (G : Type*) [Group G] [Fintype G]

omit [Fintype G] in
@[simp] lemma regularRep_apply (g h : G) (f : EuclideanSpace ℂ G) :
    regularRep G g f h = f (g⁻¹ * h) := rfl

lemma regularRep_unitary (g : G) (f k : EuclideanSpace ℂ G) :
    inner ℂ (regularRep G g f) (regularRep G g k) = inner ℂ f k := by
  simp only [PiLp.inner_apply, regularRep_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ (fun h => rfl)

def deltaOne : EuclideanSpace ℂ G := WithLp.toLp 2 (fun g => if g = 1 then 1 else 0)

omit [Fintype G] in
lemma regularRep_delta (g h : G) :
    regularRep G g (deltaOne G) h = if h = g then 1 else 0 := by
  change (if g⁻¹ * h = 1 then (1 : ℂ) else 0) = if h = g then 1 else 0
  simp [inv_mul_eq_one, eq_comm]

end
end PartialPermutation

end

end OAI
