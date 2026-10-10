import Mathlib

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma coeff_mul_mem_of_pair (F G H : Submodule ℚ R)
    (hFG : ∀ x∈F,∀ y∈G,x*y∈H) (f g : LaurentSeries R)
    (hf : ∀ k,f.coeff k∈F) (hg : ∀ k,g.coeff k∈G) (k : ℤ) :
    (f*g).coeff k∈H := by
  classical
  rw [coeff_mul]
  exact H.sum_mem (fun ij hij=>hFG _ (hf _) _ (hg _))
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
