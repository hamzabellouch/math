import Mathlib
import OAI.Combinatorics.MatchingPSD.PSDEvaluation

namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

omit [Fintype I] [DecidableEq R] in
lemma psd_isClosed : IsClosed {A : Matrix R R ℝ | A.PosSemidef} := by
  have he : {A : Matrix R R ℝ | A.PosSemidef} =
      {A : Matrix R R ℝ | Aᵀ = A} ∩
        ⋂ x : R → ℝ, {A : Matrix R R ℝ | 0 ≤ x ⬝ᵥ (A *ᵥ x)} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec, star_trivial]
    rfl
  rw [he]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_id
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    simp only [dotProduct, Matrix.mulVec]
    fun_prop

omit [Fintype I] in
lemma evaluation_continuous (B : I → Matrix R R ℝ) : Continuous (evaluation B) :=
  (evaluation B).continuous_of_finiteDimensional

end AffinePSD

end OAI
