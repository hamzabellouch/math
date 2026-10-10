import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI
noncomputable section
open scoped Topology InnerProductSpace
namespace CuntzTrace
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def rankOneGenerators : Set (H →L[ℂ] H) := {T | ∃ x y : H, T = InnerProductSpace.rankOne ℂ x y}

def finiteRankAlgebra : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H) :=
  NonUnitalStarAlgebra.adjoin ℂ (rankOneGenerators H)

def compactOperatorAlgebra : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H) :=
  (finiteRankAlgebra H).topologicalClosure

instance compactOperatorAlgebra_closed : IsClosed (compactOperatorAlgebra H : Set (H →L[ℂ] H)) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

abbrev CompactOperators := compactOperatorAlgebra H

instance : NonUnitalCStarAlgebra (CompactOperators H) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (compactOperatorAlgebra H)

variable {H}
omit [CompleteSpace H] in
lemma rankOne_isCompact (x y : H) : IsCompactOperator (InnerProductSpace.rankOne ℂ x y) := by
  have h := isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ y)
  change IsCompactOperator (fun z : H => inner ℂ y z • x)
  exact h.clm_comp (ContinuousLinearMap.toSpanSingleton ℂ x)

lemma finiteRankAlgebra_compact (T : H →L[ℂ] H) (hT : T ∈ finiteRankAlgebra H) :
    IsCompactOperator T ∧ IsCompactOperator (star T : H →L[ℂ] H) := by
  induction hT using NonUnitalStarAlgebra.adjoin_induction with
  | mem T hT =>
    obtain ⟨x,y,rfl⟩ := hT
    exact ⟨rankOne_isCompact x y, by rw [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]; exact rankOne_isCompact y x⟩
  | zero => exact ⟨isCompactOperator_zero, by simpa using (isCompactOperator_zero : IsCompactOperator (0 : H →L[ℂ] H))⟩
  | add T S _ _ hT hS =>
    exact ⟨hT.1.add hS.1, by rw [star_add]; exact hT.2.add hS.2⟩
  | mul T S _ _ hT hS =>
    exact ⟨hT.1.comp_clm S, by rw [star_mul]; exact hS.2.comp_clm (star T)⟩
  | smul c T _ hT =>
    exact ⟨hT.1.smul c, by rw [star_smul]; exact hT.2.smul (star c)⟩
  | star T _ hT => exact ⟨hT.2, by simpa only [star_star] using hT.1⟩

theorem compactOperators_areCompact (T : CompactOperators H) : IsCompactOperator (T : H →L[ℂ] H) := by
  have hc : IsClosed {T : H →L[ℂ] H | IsCompactOperator T} := isClosed_setOfPred_isCompactOperator
  apply hc.closure_subset
  apply closure_mono (fun T hT => (finiteRankAlgebra_compact T hT).1)
  exact T.2

theorem rankOne_mem_compactOperators (x y : H) :
    InnerProductSpace.rankOne ℂ x y ∈ compactOperatorAlgebra H :=
  NonUnitalStarSubalgebra.le_topologicalClosure _ (NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨x,y,rfl⟩)

abbrev StandardHilbert := lp (fun _ : ℕ => ℂ) 2

abbrev StandardCompacts := CompactOperators StandardHilbert
end CuntzTrace

end

end OAI
