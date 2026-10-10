import OAI.Computability.BinPacking.Computation.FinalCNFRowPlan

namespace OAI

namespace BinPackingGames.Foundations.PCP.FinalTableFormula

open Target Complexity

def output (table : GraphTables.Table) : Formula :=
  FinalBooleanVerifier.cnf (FinalCNFPattern.tableGraph table) (Equiv.refl _) (Equiv.refl _)

theorem satisfiable_iff (table : GraphTables.Table) :
    (output table).Satisfiable ↔ (GraphTables.semantics table).Satisfiable :=
  (FinalBooleanVerifier.cnf_satisfiable_iff (FinalCNFPattern.tableGraph table)
    (Equiv.refl _) (Equiv.refl _)).trans
      ((GraphTables.semantics table).satisfiable_reindex (Equiv.refl _) (Equiv.refl _)
        FinalCNFPattern.labelEquiv.symm)

@[simp] theorem variable_count (table : GraphTables.Table) :
    (output table).variables = table.vertices * 6 + table.darts * 36864 :=
  FinalBooleanVerifier.cnf_variable_count _ (Equiv.refl _) (Equiv.refl _)

@[simp] theorem clause_count (table : GraphTables.Table) :
    (output table).clauses.length = table.darts * 40960 :=
  FinalBooleanVerifier.cnf_clause_count _ (Equiv.refl _) (Equiv.refl _)

theorem nonempty (table : GraphTables.Table) (hd : 0 < table.darts) :
    (output table).clauses ≠ [] :=
  FinalBooleanVerifier.cnf_nonempty _ (Equiv.refl _) (Equiv.refl _) hd

theorem tableGraph_rejectionCount (table : GraphTables.Table)
    (labeling : Fin table.vertices → FinalBooleanVerifier.Label) :
    (FinalCNFPattern.tableGraph table).rejectionCount labeling =
      (GraphTables.semantics table).rejectionCount
        (fun v => FinalCNFPattern.labelEquiv (labeling v)) := by
  have h := (GraphTables.semantics table).reindex_rejectionCount
    (Equiv.refl _) (Equiv.refl _) FinalCNFPattern.labelEquiv.symm
    (fun v => FinalCNFPattern.labelEquiv (labeling v))
  simpa [FinalCNFPattern.tableGraph, ConstraintGraph.labelingEquiv] using h

theorem tableGraph_count_lower (table : GraphTables.Table) (walkLength : Nat)
    (hgap : ∀ labeling : Fin table.vertices → GraphTables.Label,
      table.darts ≤ walkLength * (GraphTables.semantics table).rejectionCount labeling)
    (labeling : Fin table.vertices → FinalBooleanVerifier.Label) :
    Fintype.card (Fin table.darts) ≤
      walkLength * (FinalCNFPattern.tableGraph table).rejectionCount labeling := by
  rw [Fintype.card_fin, tableGraph_rejectionCount]
  exact hgap _

theorem clauseGap (table : GraphTables.Table) (hd : 0 < table.darts)
    (hgap : ∀ labeling : Fin table.vertices → GraphTables.Label,
      table.darts ≤ FinalConstants.walkLength *
        (GraphTables.semantics table).rejectionCount labeling) :
    Hastad.SourceGap.ClauseGap (output table) PCPIteration.finalClauseGap := by
  let : Nonempty (Fin table.darts) := ⟨⟨0, hd⟩⟩
  exact Hastad.SourceNonempty.cnf_clauseGap_unit (FinalCNFPattern.tableGraph table)
    (Equiv.refl _) (Equiv.refl _) FinalConstants.walkLength
    FinalConstants.walkLength_positive (tableGraph_count_lower table _ hgap)

theorem total_size_le (table : GraphTables.Table) :
    (output table).variables + (output table).clauses.length ≤
      77824 * (table.vertices + table.darts) := by
  have hv := variable_count table
  have hc := clause_count table
  omega

noncomputable def sizePolynomial : Polynomial Nat :=
  Polynomial.C 77824 * Polynomial.X + Polynomial.C 2 +
    (Polynomial.C 40960 * Polynomial.X) *
      (Polynomial.C 3 * (Polynomial.C 36864 * Polynomial.X + Polynomial.C 2))

theorem sizePolynomial_eval (N : Nat) :
    sizePolynomial.eval N = 77824 * N + 2 + (40960 * N) * (3 * (36864 * N + 2)) := by
  simp [sizePolynomial]

theorem formulaBits_length_le_polynomial (table : GraphTables.Table) :
    (formulaBits (output table)).length ≤
      sizePolynomial.eval (GraphTables.tableBits table).length := by
  have hinput := GraphTableComplexity.size_add_two_le_bits table
  have hv : (output table).variables ≤ 36864 * (GraphTables.tableBits table).length := by
    rw [variable_count]
    omega
  have hc : (output table).clauses.length ≤ 40960 * (GraphTables.tableBits table).length := by
    rw [clause_count]
    omega
  have hsum : (output table).variables + (output table).clauses.length + 2 ≤
      77824 * (GraphTables.tableBits table).length + 2 := by omega
  have hproduct := Nat.mul_le_mul hc (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hv 2))
  rw [sizePolynomial_eval]
  exact (formulaBits_length_le (output table)).trans (Nat.add_le_add hsum hproduct)

end BinPackingGames.Foundations.PCP.FinalTableFormula

namespace BinPackingGames.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

def run (H : BaseTable) : Nat → Input → Input := AmplificationIteration.run (step H)

def runTables (H : BaseTable) : Nat → GraphTables.Table → GraphTables.Table :=
  AmplificationIteration.run (build H)

theorem run_val (H : BaseTable) (n : Nat) (input : Input) :
    (run H n input).val = runTables H n input.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change build H (run H n input).val = build H (runTables H n input.val)
      rw [ih]

def iterationCount (F : Formula) : Nat := AmplificationIteration.rounds (size (initial F))

def output (H : BaseTable) (F : Formula) : Input := run H (iterationCount F) (initial F)

def outputTable (H : BaseTable) (F : Formula) : GraphTables.Table :=
  runTables H (iterationCount F) (RawInitialTables.table F)

theorem output_val (H : BaseTable) (F : Formula) : (output H F).val = outputTable H F :=
  run_val H (iterationCount F) (initial F)

def gapMap (H : BaseTable) (F : Formula) : Formula := FinalTableFormula.output (outputTable H F)

opaque degreeData : {n : Nat // sizeFactor ≤ 2 ^ n} :=
  ⟨AmplificationIteration.rounds sizeFactor, (AmplificationIteration.rounds_large sizeFactor).le⟩

def polynomialDegree : Nat := degreeData.val

theorem sizeFactor_le_power : sizeFactor ≤ 2 ^ polynomialDegree :=
  degreeData.property

theorem run_completeness (H : BaseTable) (n : Nat) (input : Input)
    (sat : Satisfiable input) : Satisfiable (run H n input) :=
  AmplificationIteration.run_preserves (step H) Satisfiable (step_completeness H) n input sat

theorem output_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    Satisfiable (output H F) :=
  run_completeness H _ _ ((initial_satisfiable_iff F).mpr sat)

theorem gapMap_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    (gapMap H F).Satisfiable := by
  apply (FinalTableFormula.satisfiable_iff (outputTable H F)).mpr
  rw [← output_val]
  exact output_completeness H F sat

theorem output_darts_positive (H : BaseTable) (F : Formula) : 0 < (outputTable H F).darts := by
  rw [← output_val]
  exact (output H F).property

theorem gapMap_nonempty (H : BaseTable) (F : Formula) : (gapMap H F).clauses ≠ [] :=
  FinalTableFormula.nonempty (outputTable H F) (output_darts_positive H F)

theorem run_size (H : BaseTable) (n : Nat) (input : Input) :
    size (run H n input) ≤ sizeFactor ^ n * size input :=
  AmplificationIteration.run_size (step H) size sizeFactor (step_size H) n input

theorem output_size (H : BaseTable) (F : Formula) :
    size (output H F) ≤ (2 * size (initial F)) ^ polynomialDegree * size (initial F) :=
  AmplificationIteration.run_size_polynomial (step H) size (size_positive (initial F))
    sizeFactor_le_power (step_size H) (initial F)

theorem initial_size_le (F : Formula) : size (initial F) ≤ 7 * (formulaBits F).length :=
  RawInitialMachineBudget.graph_size_bound F

theorem output_size_le_input (H : BaseTable) (F : Formula) :
    (outputTable H F).vertices + (outputTable H F).darts ≤
      (14 * (formulaBits F).length) ^ polynomialDegree * (7 * (formulaBits F).length) := by
  rw [← output_val]
  have h := initial_size_le F
  exact (output_size H F).trans
    (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) h)

noncomputable def tableSizePolynomial : Polynomial Nat :=
  (Polynomial.C 14 * Polynomial.X) ^ polynomialDegree * (Polynomial.C 7 * Polynomial.X)

theorem tableSizePolynomial_eval (N : Nat) :
    tableSizePolynomial.eval N = (14 * N) ^ polynomialDegree * (7 * N) := by
  simp only [tableSizePolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]

noncomputable def tableBitsPolynomial : Polynomial Nat :=
  (GraphTableComplexity.encodingPolynomial 64).comp tableSizePolynomial

theorem output_bits_le (H : BaseTable) (F : Formula) :
    (GraphTables.tableBits (outputTable H F)).length ≤ tableBitsPolynomial.eval (formulaBits F).length := by
  rw [tableBitsPolynomial, Polynomial.eval_comp, tableSizePolynomial_eval]
  exact GraphTableComplexity.bits_le_of_size_le _ (output_size_le_input H F)

noncomputable def formulaBitsPolynomial : Polynomial Nat :=
  FinalTableFormula.sizePolynomial.comp tableBitsPolynomial

theorem gapMap_bits_le (H : BaseTable) (F : Formula) :
    (formulaBits (gapMap H F)).length ≤ formulaBitsPolynomial.eval (formulaBits F).length := by
  rw [formulaBitsPolynomial, Polynomial.eval_comp]
  exact (FinalTableFormula.formulaBits_length_le_polynomial (outputTable H F)).trans
    (MachineComposition.natPolynomial_eval_mono _ (output_bits_le H F))

end BinPackingGames.Foundations.PCP.TableIteration

namespace BinPackingGames.Foundations.PCP.TableGapReduction

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

end BinPackingGames.Foundations.PCP.TableGapReduction

namespace BinPackingCompleteness.PCPSource

open BinPackingGames.Foundations Target PCP SourceClause
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
end BinPackingCompleteness.PCPSource

end OAI
