import Mathlib
import OAI.Computability.VertexCover.PCP.TableIteration
import OAI.Computability.VertexCover.PCP.RoundTableGap

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                          
section

namespace UniqueGames.Foundations.PCP.TableGapReduction

open RoundTables TableIteration SpectralReturn Target

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem run_gap (n : Nat) (input : Input) :
    min (2 ^ n * gap input) FinalConstants.cap ≤ gap (TableIteration.run H n input) :=
  AmplificationIteration.run_gap (step H) gap FinalConstants.cap FinalConstants.cap_positive.le
    (RoundTableGap.step_gap H certificate) n input

theorem output_gap (F : Formula) (unsat : ¬ F.Satisfiable) :
    FinalConstants.cap ≤ gap (TableIteration.output H F) := by
  have hu : ¬ Satisfiable (initial F) := fun sat => unsat ((initial_satisfiable_iff F).mp sat)
  exact AmplificationIteration.run_reaches_cap (step H) gap FinalConstants.cap
    FinalConstants.cap_positive.le FinalConstants.cap_le_one (RoundTableGap.step_gap H certificate)
    (size (initial F)) (initial F) (gap_nonnegative (initial F))
    (one_le_size_mul_gap (initial F) hu)

theorem output_satisfiable_iff (F : Formula) :
    Satisfiable (TableIteration.output H F) ↔ F.Satisfiable := by
  constructor
  · intro sat
    by_contra unsat
    have bound := output_gap H certificate F unsat
    rw [(gap_eq_zero_iff (TableIteration.output H F)).mpr sat] at bound
    exact (not_le_of_gt FinalConstants.cap_positive) bound
  · exact TableIteration.output_completeness H F

theorem gapMap_satisfiable_iff (F : Formula) : (gapMap H F).Satisfiable ↔ F.Satisfiable := by
  rw [gapMap, FinalTableFormula.satisfiable_iff, ← output_val]
  exact output_satisfiable_iff H certificate F

theorem output_count_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (labeling : Fin (outputTable H F).vertices → GraphTables.Label) :
    (outputTable H F).darts ≤ FinalConstants.walkLength *
      (GraphTables.semantics (outputTable H F)).rejectionCount labeling := by
  have hp := output_darts_positive H F
  let : Nonempty (Fin (outputTable H F).darts) := ⟨⟨0, hp⟩⟩
  have bound := output_gap H certificate F unsat
  change FinalConstants.cap ≤ (GraphTables.semantics (TableIteration.output H F).val).gap at bound
  rw [output_val] at bound
  have count := ((GraphTables.semantics (outputTable H F)).le_gap_iff FinalConstants.cap).mp bound labeling
  simp only [Fintype.card_fin] at count
  have ht : (0 : ℝ) < FinalConstants.walkLength := Nat.cast_pos.mpr FinalConstants.walkLength_positive
  have divided : ((outputTable H F).darts : ℝ) / FinalConstants.walkLength ≤
      ((GraphTables.semantics (outputTable H F)).rejectionCount labeling : ℝ) := by
    simpa only [FinalConstants.cap, one_div_mul_eq_div] using count
  have multiplied := (div_le_iff₀ ht).mp divided
  exact_mod_cast (show ((outputTable H F).darts : ℝ) ≤ (FinalConstants.walkLength : ℝ) *
      ((GraphTables.semantics (outputTable H F)).rejectionCount labeling : ℝ) by
    simpa only [mul_comm] using multiplied)

theorem gapMap_clauseGap (F : Formula) (unsat : ¬ F.Satisfiable) :
    Hastad.SourceGap.ClauseGap (gapMap H F) PCPIteration.finalClauseGap :=
  FinalTableFormula.clauseGap (outputTable H F) (output_darts_positive H F)
    (output_count_gap H certificate F unsat)

omit certificate in
theorem finalClauseGap_le_one : PCPIteration.finalClauseGap ≤ 1 := by
  have hw : (1 : ℚ) ≤ (FinalConstants.walkLength : ℚ) := by
    exact_mod_cast FinalConstants.walkLength_positive
  have hd : (0 : ℚ) < 40960 * (FinalConstants.walkLength : ℚ) := by positivity
  rw [PCPIteration.finalClauseGap, div_le_one hd]
  linarith

end UniqueGames.Foundations.PCP.TableGapReduction

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
