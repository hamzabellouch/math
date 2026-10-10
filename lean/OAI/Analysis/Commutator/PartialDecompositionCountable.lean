import Mathlib
import OAI.Analysis.Commutator.PartialDecomposition
import OAI.Analysis.Commutator.OrthogonalCountability

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.PartialIsometryOrder.PartialDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : PartialDecomposition M p)

theorem countable : Countable D.I := by
  have hx (i : D.I) : ∃ x : H,(D.v i).val x≠0 := by
    by_contra hn
    push Not at hn
    exact D.nonzero i (ContinuousLinearMap.ext hn)
  choose x hx using hx
  apply Kadison.countable_orthogonal_family (fun i => (D.v i).val (x i)) hx
  intro i j hij
  rw [←ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (x i) ((star (D.v i).val*(D.v j).val) (x j))=0
  rw [D.cross i j hij]
  simp

end Kadison.PartialIsometryOrder.PartialDecomposition

end

end
end

end OAI
