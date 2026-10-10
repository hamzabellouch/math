import OAI.Computability.PerfectCompleteness.Reduction.FixedTarget

namespace OAI


namespace PerfectCompleteness.FixedTargetValue


open UniqueGamesTheorem.Foundations Target
open FixedParameters FixedRows FixedPreliminaryGame
open scoped Classical

noncomputable section

private theorem packed_value_le (formula : Formula) [NeZero formula.clauses.length]
    (nonempty : formula.clauses ≠ [])
    (distinct : ∀ clause ∈ formula.clauses, ∀ i j : Fin 3,
      clause[i].variableIndex = clause[j].variableIndex → i = j)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ) (hδ : 0 < δ) :
    (NormalizedTarget.construct (branch := branch) (n := n) (t := t)
      rows repeats hn hbranch hrows δ ⟨formula, nonempty, distinct⟩).value ≤
      PreliminaryOutput.value
        (fun index : Fin formula.clauses.length =>
          ({ clause := PCP.clauseAt formula index
             distinct := fun i j same => distinct _ (List.getElem_mem index.isLt) i j same } :
            SourceClause.NormalizedClause formula.variables))
        branch n t rows repeats hn hbranch hrows + (δ : ℝ) / 3 := by
  have clauses_eq :
      NormalizedSourceInput.clauses ⟨formula, nonempty, distinct⟩ =
        (fun index : Fin formula.clauses.length =>
          ({ clause := PCP.clauseAt formula index
             distinct := fun i j same => distinct _ (List.getElem_mem index.isLt) i j same } :
            SourceClause.NormalizedClause formula.variables)) := by
    funext index
    rfl
  have native :
      (NormalizedTarget.construct (branch := branch) (n := n) (t := t)
        rows repeats hn hbranch hrows δ ⟨formula, nonempty, distinct⟩).value ≤
        PreliminaryOutput.value (NormalizedSourceInput.clauses ⟨formula, nonempty, distinct⟩)
          branch n t rows repeats hn hbranch hrows + (δ : ℝ) / 3 := by
    simpa only [PreliminaryOutput.value] using
      (NormalizedTarget.value_le (branch := branch) (n := n) (t := t)
        rows repeats hn hbranch hrows δ ⟨formula, nonempty, distinct⟩ hδ)
  rw [clauses_eq] at native
  exact native

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem value_le (input : List Bool) :
    (FixedTarget.construct p input).value ≤
      FixedPreliminaryGame.value p input + (δ : ℝ) / 3 :=
  packed_value_le (PCPSource.normalizedFormula (BinaryLanguage.totalRename input))
    (PCPSource.normalizedFormula_nonempty (BinaryLanguage.totalRename input))
    (PCPSource.normalizedFormula_distinct (BinaryLanguage.totalRename input))
    (branch p) p.plan.depth (sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
    (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1)) δ hδ

end
end PerfectCompleteness.FixedTargetValue

end OAI
