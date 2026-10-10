import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralOrthogonal

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

lemma finiteOrthogonalColumn_weighted (n : ℕ) (M N : FinMatrix A n)
    (r : ℝ) (hr : r ≠ 0) :
    finiteOrthogonalColumn n M N * star (finiteOrthogonalColumn n M N) +
      finiteOrthogonalColumn n (r • M) (-(r⁻¹ • N)) *
        star (finiteOrthogonalColumn n (r • M) (-(r⁻¹ • N))) =
    matrixInterleaveRaw n ((1+r*r) • (M*star M),(1+r⁻¹*r⁻¹) • (N*star N)) := by
  apply CStarMatrix.ext
  rintro ⟨i,s⟩ ⟨j,t⟩
  fin_cases s <;> fin_cases t <;>
    simp [finiteOrthogonalColumn,matrixInterleaveRaw_entry',CStarMatrix.mul_apply,
      CStarMatrix.star_apply,Fintype.sum_prod_type,
      CStarMatrix.add_apply,CStarMatrix.smul_apply,star_smul,
      smul_smul,Finset.smul_sum,
      hr]
  all_goals simp [add_smul,Finset.sum_add_distrib]
end CuntzPureness

end

end OAI
