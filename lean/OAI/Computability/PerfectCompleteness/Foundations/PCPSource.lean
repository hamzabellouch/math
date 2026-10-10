import OAI.Computability.PerfectCompleteness.Foundations.NormalizationLemmas
import OAI.Computability.PerfectCompleteness.Machines.BinaryFormulaLemmas
import OAI.Computability.PerfectCompleteness.Repetition.SourceAmplification
import OAI.Computability.UniqueGames.PCP.ExpanderTables
import OAI.Computability.UniqueGames.PCP.TableGapReductionLemmas

namespace OAI

section

namespace PerfectCompleteness.PCPSource

open UniqueGamesTheorem.Foundations Target PCP SourceClause
open scoped BigOperators

noncomputable section

def baseTable : RoundTables.BaseTable :=
  Classical.choose ExpanderTables.exists_base_table

theorem baseTable_certificate :
    SpectralReturn.SpectralCertificate (ExpanderTables.graph baseTable) (1 / 100 : ℝ) :=
  Classical.choose_spec ExpanderTables.exists_base_table

def rawFormula (F : Formula) : Formula := TableIteration.gapMap baseTable F

def normalizedFormula (F : Formula) : Formula := Normalization.normalize (rawFormula F)

theorem rawFormula_nonempty (F : Formula) : (rawFormula F).clauses ≠ [] :=
  TableIteration.gapMap_nonempty baseTable F

theorem normalizedFormula_nonempty (F : Formula) : (normalizedFormula F).clauses ≠ [] :=
  Normalization.normalize_nonempty (rawFormula F) (rawFormula_nonempty F)

theorem normalizedFormula_satisfiable_iff (F : Formula) :
    (normalizedFormula F).Satisfiable ↔ F.Satisfiable := by
  exact (Normalization.normalize_satisfiable_iff (rawFormula F)).trans
    (TableGapReduction.gapMap_satisfiable_iff baseTable baseTable_certificate F)

theorem normalizedFormula_distinct (F : Formula)
    (c : Clause (normalizedFormula F).variables) (hc : c ∈ (normalizedFormula F).clauses)
    (i j : Fin 3) (same : (c)[i].variableIndex = (c)[j].variableIndex) : i = j :=
  Normalization.normalize_distinct (rawFormula F) c hc i j same

def baseDenominator : Nat := 40960 * FinalConstants.walkLength

def sourceDenominator : Nat := 13 * baseDenominator

def sourceGap : ℚ := 1 / (sourceDenominator : ℚ)

theorem baseDenominator_pos : 0 < baseDenominator :=
  Nat.mul_pos (by decide) FinalConstants.walkLength_positive

theorem sourceDenominator_pos : 0 < sourceDenominator :=
  Nat.mul_pos (by decide) baseDenominator_pos

theorem sourceGap_pos : 0 < sourceGap := by
  apply one_div_pos.mpr
  exact_mod_cast sourceDenominator_pos

theorem sourceGap_le_one : sourceGap ≤ 1 := by
  have hden : (0 : ℚ) < sourceDenominator := by exact_mod_cast sourceDenominator_pos
  have hone : (1 : ℚ) ≤ sourceDenominator := by exact_mod_cast sourceDenominator_pos
  exact (div_le_one hden).mpr hone

theorem finalClauseGap_eq : PCPIteration.finalClauseGap = 1 / (baseDenominator : ℚ) := by
  simp only [PCPIteration.finalClauseGap, baseDenominator, Nat.cast_mul, Nat.cast_ofNat]

theorem sourceGap_eq : sourceGap = PCPIteration.finalClauseGap / 13 := by
  rw [finalClauseGap_eq]
  simp only [sourceGap, sourceDenominator, Nat.cast_mul, Nat.cast_ofNat, div_div, mul_comm]

theorem rawFormula_count_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (A : Fin (rawFormula F).variables → Bool) :
    1 * (rawFormula F).clauses.length ≤
      baseDenominator * NameCompaction.failedCount (rawFormula F) A := by
  have hr := (TableGapReduction.gapMap_clauseGap baseTable baseTable_certificate F unsat).2 A
  have hr' : (PCPIteration.finalClauseGap : ℝ) * ((rawFormula F).clauses.length : ℝ) ≤
      (NameCompaction.failedCount (rawFormula F) A : ℝ) :=
    hr.trans_eq (congrArg (fun count : Nat => (count : ℝ))
      (NameCompaction.verifier_failureCount (rawFormula F) A))
  have hq : PCPIteration.finalClauseGap * ((rawFormula F).clauses.length : ℚ) ≤
      (NameCompaction.failedCount (rawFormula F) A : ℚ) := by
    exact_mod_cast hr'
  rw [finalClauseGap_eq, one_div_mul_eq_div] at hq
  have hden : (0 : ℚ) < baseDenominator := by exact_mod_cast baseDenominator_pos
  have h := (div_le_iff₀ hden).mp hq
  have hnat : (rawFormula F).clauses.length ≤
      baseDenominator * NameCompaction.failedCount (rawFormula F) A := by
    exact_mod_cast (show ((rawFormula F).clauses.length : ℚ) ≤
      (baseDenominator : ℚ) * (NameCompaction.failedCount (rawFormula F) A : ℚ) by
        simpa only [mul_comm] using h)
  simpa only [Nat.one_mul] using hnat

theorem normalizedFormula_count_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (A : Fin (normalizedFormula F).variables → Bool) :
    (normalizedFormula F).clauses.length ≤
      sourceDenominator * NameCompaction.failedCount (normalizedFormula F) A := by
  simpa only [normalizedFormula, sourceDenominator, Nat.one_mul] using
    Normalization.normalize_gap (rawFormula F) 1 baseDenominator
      (rawFormula_count_gap F unsat) A

def clauseFamily (F : Formula) :
    Fin (normalizedFormula F).clauses.length → NormalizedClause (normalizedFormula F).variables :=
  fun c =>
    { clause := clauseAt (normalizedFormula F) c
      distinct := fun i j same => normalizedFormula_distinct F _
        (List.getElem_mem c.isLt) i j same }

instance clauseCount_neZero (F : Formula) : NeZero (normalizedFormula F).clauses.length :=
  ⟨Nat.ne_of_gt (List.length_pos_iff.mpr (normalizedFormula_nonempty F))⟩

theorem failedCount_eq_fin_sum (F : Formula) (A : Fin F.variables → Bool) :
    NameCompaction.failedCount F A =
      ∑ i : Fin F.clauses.length, if (clauseAt F i).eval A then 0 else 1 := by
  unfold NameCompaction.failedCount
  rw [← NameCompaction.evaluations_allIndices, VerifierToCNF.count_false_map_sum]
  simp [allIndices, List.finRange, List.map_ofFn, List.sum_ofFn]

theorem violatedCount_eq_failedCount (F : Formula)
    (A : Fin (normalizedFormula F).variables → Bool) :
    SourceGame.violatedCount (clauseFamily F) A =
      NameCompaction.failedCount (normalizedFormula F) A := by
  rw [failedCount_eq_fin_sum]
  rfl

theorem clauseGap (F : Formula) (unsat : ¬ F.Satisfiable) :
    SourceAmplification.ClauseGap (clauseFamily F) sourceGap := by
  intro A
  have hnat := normalizedFormula_count_gap F unsat A
  have hq : ((normalizedFormula F).clauses.length : ℚ) ≤
      (sourceDenominator : ℚ) * (NameCompaction.failedCount (normalizedFormula F) A : ℚ) := by
    exact_mod_cast hnat
  rw [← violatedCount_eq_failedCount] at hq
  change (1 / (sourceDenominator : ℚ)) * ((normalizedFormula F).clauses.length : ℚ) ≤ _
  rw [one_div_mul_eq_div]
  have hden : (0 : ℚ) < sourceDenominator := by exact_mod_cast sourceDenominator_pos
  exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hq)

def source (F : Formula) := SourceGame.game (clauseFamily F)

theorem source_complete (F : Formula) (sat : F.Satisfiable) : (source F).value = 1 := by
  obtain ⟨A, hA⟩ := (normalizedFormula_satisfiable_iff F).mpr sat
  exact SourceGame.completeness_value (clauseFamily F) A
    (fun c => hA _ (List.getElem_mem c.isLt))

theorem source_sound (F : Formula) (unsat : ¬ F.Satisfiable) :
    (source F).value ≤ 1 - ((sourceGap / 3 : ℚ) : ℝ) :=
  SourceAmplification.source_value_le (clauseFamily F) (clauseGap F unsat)

def repetitionLength (σ : ℚ) (hσ : 0 < σ) : Nat :=
  SourceAmplification.repetitionLength sourceGap σ sourceGap_pos sourceGap_le_one hσ

theorem repetitionLength_positive (σ : ℚ) (hσ : 0 < σ) : 0 < repetitionLength σ hσ :=
  (SourceAmplification.repetitionLength_spec sourceGap σ sourceGap_pos sourceGap_le_one hσ).1

def amplifiedSource (F : Formula) (σ : ℚ) (hσ : 0 < σ) :=
  (source F).repetition (repetitionLength σ hσ)

theorem amplifiedSource_complete (F : Formula) (sat : F.Satisfiable)
    (σ : ℚ) (hσ : 0 < σ) : (amplifiedSource F σ hσ).value = 1 := by
  obtain ⟨A, hA⟩ := (normalizedFormula_satisfiable_iff F).mpr sat
  exact SourceAmplification.repeated_completeness_value (clauseFamily F) A
    (fun c => hA _ (List.getElem_mem c.isLt)) (repetitionLength σ hσ)

theorem amplifiedSource_sound (F : Formula) (unsat : ¬ F.Satisfiable)
    (σ : ℚ) (hσ : 0 < σ) : (amplifiedSource F σ hσ).value < (σ : ℝ) :=
  SourceAmplification.repeated_source_value_lt (clauseFamily F) sourceGap σ
    sourceGap_pos sourceGap_le_one hσ (clauseGap F unsat)

def binarySource (F : BinaryFormula.Formula) := source (BinaryFormula.dense F)

theorem binarySource_complete (F : BinaryFormula.Formula) (sat : F.Satisfiable) :
    (binarySource F).value = 1 :=
  source_complete (BinaryFormula.dense F) (BinaryFormula.dense_completeness F sat)

theorem binarySource_sound (F : BinaryFormula.Formula) (unsat : ¬ F.Satisfiable) :
    (binarySource F).value ≤ 1 - ((sourceGap / 3 : ℚ) : ℝ) :=
  source_sound (BinaryFormula.dense F) (fun sat => unsat (BinaryFormula.dense_reflects F sat))

def binaryAmplifiedSource (F : BinaryFormula.Formula) (σ : ℚ) (hσ : 0 < σ) :=
  amplifiedSource (BinaryFormula.dense F) σ hσ

theorem binaryAmplifiedSource_complete (F : BinaryFormula.Formula) (sat : F.Satisfiable)
    (σ : ℚ) (hσ : 0 < σ) : (binaryAmplifiedSource F σ hσ).value = 1 :=
  amplifiedSource_complete (BinaryFormula.dense F)
    (BinaryFormula.dense_completeness F sat) σ hσ

theorem binaryAmplifiedSource_sound (F : BinaryFormula.Formula) (unsat : ¬ F.Satisfiable)
    (σ : ℚ) (hσ : 0 < σ) : (binaryAmplifiedSource F σ hσ).value < (σ : ℝ) :=
  amplifiedSource_sound (BinaryFormula.dense F)
    (fun sat => unsat (BinaryFormula.dense_reflects F sat)) σ hσ

end
end PerfectCompleteness.PCPSource

end

end OAI
