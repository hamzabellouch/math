import Mathlib
import OAI.Combinatorics.IndependentSets.Fourier.Gap
import OAI.Combinatorics.IndependentSets.PCP.PCPIteration

namespace OAI

noncomputable section
namespace IndependentSetsGames.Foundations.PCP.PCPIteration
open FiniteGraph

variable (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
  (F : Target.Formula) {n m : Nat}
  (vertices : (output addresses complete F).Vertex ≃ Fin n)
  (darts : (output addresses complete F).Dart ≃ Fin m)

def finalCNF : Target.Formula :=
  FinalBooleanVerifier.cnf (output addresses complete F).graph vertices darts

theorem finalCNF_satisfiable_iff :
    (finalCNF addresses complete F vertices darts).Satisfiable ↔ F.Satisfiable :=
  (FinalBooleanVerifier.cnf_satisfiable_iff _ vertices darts).trans
    (output_satisfiable_iff addresses complete F)

theorem finalCNF_clause_count :
    (finalCNF addresses complete F vertices darts).clauses.length = m * 40960 :=
  FinalBooleanVerifier.cnf_clause_count _ vertices darts

theorem finalCNF_variable_count :
    (finalCNF addresses complete F vertices darts).«variables» = n * 6 + m * 36864 :=
  FinalBooleanVerifier.cnf_variable_count _ vertices darts

theorem finalCNF_nonempty : (finalCNF addresses complete F vertices darts).clauses ≠ [] := by
  have hm : Fintype.card (output addresses complete F).Dart = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr darts
  have hpositive : 0 < m := hm ▸ (Fintype.card_pos :
    0 < Fintype.card (output addresses complete F).Dart)
  exact FinalBooleanVerifier.cnf_nonempty _ vertices darts hpositive

theorem finalCNF_gap (unsat : ¬ F.Satisfiable)
    (assignment : Fin (finalCNF addresses complete F vertices darts).«variables» → Bool) :
    (finalCNF addresses complete F vertices darts).clauses.length ≤
      (FinalConstants.walkLength * 40960) *
        NameCompaction.failedCount (finalCNF addresses complete F vertices darts) assignment := by
  have source (labeling : (output addresses complete F).Vertex → Label) :
      1 * Fintype.card (output addresses complete F).Dart ≤
        FinalConstants.walkLength * (output addresses complete F).graph.rejectionCount labeling := by
    simpa only [one_mul, Bundle.rejectionCount] using output_count_gap addresses complete F unsat labeling
  simpa only [one_mul, finalCNF] using FinalBooleanVerifier.cnf_gap
    (output addresses complete F).graph vertices darts 1 FinalConstants.walkLength source assignment

theorem finalCNF_clauseGap (unsat : ¬ F.Satisfiable) :
    Hastad.SourceGap.ClauseGap (finalCNF addresses complete F vertices darts) finalClauseGap :=
  Hastad.SourceNonempty.cnf_clauseGap_unit (output addresses complete F).graph
    vertices darts FinalConstants.walkLength FinalConstants.walkLength_positive
    (output_count_gap addresses complete F unsat)

theorem finalCNF_total_size :
    (finalCNF addresses complete F vertices darts).«variables» +
        (finalCNF addresses complete F vertices darts).clauses.length ≤
      77824 * (output addresses complete F).size := by
  have hn : Fintype.card (output addresses complete F).Vertex = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr vertices
  have hm : Fintype.card (output addresses complete F).Dart = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr darts
  have hsize : (output addresses complete F).size = n + m := congrArg₂ Nat.add hn hm
  calc
    _ = n * 6 + m * 36864 + m * 40960 :=
      congrArg₂ Nat.add (finalCNF_variable_count addresses complete F vertices darts)
        (finalCNF_clause_count addresses complete F vertices darts)
    _ ≤ 77824 * (n + m) := by omega
    _ = 77824 * (output addresses complete F).size :=
      congrArg (fun k => 77824 * k) hsize.symm

theorem finalCNF_polynomial_size :
    (finalCNF addresses complete F vertices darts).«variables» +
        (finalCNF addresses complete F vertices darts).clauses.length ≤
      77824 * ((2 * (10 * F.clauses.length + 2)) ^ polynomialDegree *
        (10 * F.clauses.length + 2)) :=
  (finalCNF_total_size addresses complete F vertices darts).trans
    (Nat.mul_le_mul_left _ (output_size_clause_bound addresses complete F))

end IndependentSetsGames.Foundations.PCP.PCPIteration

end

end OAI
