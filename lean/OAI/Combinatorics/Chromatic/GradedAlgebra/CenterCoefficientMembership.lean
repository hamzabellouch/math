import Mathlib
import OAI.Combinatorics.Chromatic.Walls.HNSpanning

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
variable {σ A : Type*} [CommRing A] [Algebra ℚ A]

lemma evalRat_mem_of_coeff (M : Submodule ℚ A) (p : MvPolynomial σ A)
    (hp : ∀ s,p.coeff s∈M) (v : σ → ℚ) : evalRat v p∈M := by
  classical
  rw [p.as_sum,map_sum]
  apply M.sum_mem
  intro s hs
  rw [evalRat_monomial]
  exact M.smul_mem _ (hp s)

end ElementaryPositivity.CenterCalculus

end

end OAI
