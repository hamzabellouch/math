import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.TableIteration
import OAI.Combinatorics.IndependentSets.Expansion.PoweringPortReindex

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RoundTableGap

open RoundTables
open PoweringWalks SpectralReturn

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem powered_count_gap (input : Input)
    (labeling : Fin (powered H input.val).vertices → Fin alphabet) :
    RoundGap.poweredLower (gap input) * ((powered H input.val).darts : ℝ) ≤
      ((GenericGraphTables.semantics (powered H input.val)).rejectionCount labeling : ℝ) := by
  let old := PreprocessingOverlayTables.overlay
    (PreprocessingTables.padded H input.val) (PreprocessingTables.overlayFamily H input.val)
  have hd : 0 < (PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree := by omega
  let : Nonempty (Fin ((PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree)) := ⟨⟨0, hd⟩⟩
  have spectral : SpectralCertificate (lazyGraph (PortTables.portGraph old)) (31 / 32 : ℝ) :=
    LazySpectral.lazy_certificate_31_32 (PortTables.portGraph old)
      (PreprocessingGuarantees.overlay_certificate H certificate input.val)
  have lower := PreprocessingGuarantees.gap_transfer_real H certificate input.val input.property
    (gap input) (gap_nonnegative input)
    (by simpa only [Fintype.card_fin] using
      ((GraphTables.semantics input.val).le_gap_iff (gap input)).mp le_rfl)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := Nat.cast_pos.mpr Preprocessing.sizeFactor_positive
  have hn : walkParameter = 2 * PoweringSoundness.center 64 FinalConstants.windowHalf :=
    walkParameter_eq
  have bound := PoweringPortReindex.lazy_table_uniform_count_gap_at old
    (PreprocessingTables.vertices_positive input.val) hd (31 / 32) spectral
    FinalConstants.windowHalf FinalConstants.windowHalf_positive walkParameter hn
    (gap input / Preprocessing.sizeFactor) (div_nonneg (gap_nonnegative input) hs.le)
    lower labeling
  have hw : walkParameter + 1 = FinalConstants.walkLength := by
    rw [walkParameter_eq]
    rfl
  rw [hw] at bound
  simp only [RoundGap.poweredLower, PoweringFinalConstants.card_alphabet, FinalConstants.cap]
  exact bound

theorem build_count_gap (input : Input)
    (labeling : Fin (build H input.val).vertices → GraphTables.Label) :
    min (2 * gap input) FinalConstants.cap * ((build H input.val).darts : ℝ) ≤
      ((GraphTables.semantics (build H input.val)).rejectionCount labeling : ℝ) := by
  have h := AlphabetTableBounds.gap_transfer_real alphabet_positive (powered H input.val)
    (RoundGap.poweredLower (gap input))
    (RoundGap.poweredLower_nonnegative (gap input) (gap_nonnegative input))
    (powered_count_gap H certificate input) labeling
  have scalar : min (2 * gap input) FinalConstants.cap ≤
      RoundGap.poweredLower (gap input) / 12288 := by
    simpa only [RoundGap.poweredLower, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq] using
      PoweringFinalConstants.composed_scaled_gap (gap input) (gap_nonnegative input)
  exact (mul_le_mul_of_nonneg_right scalar (Nat.cast_nonneg _)).trans h

theorem step_gap (input : Input) :
    min (2 * gap input) FinalConstants.cap ≤ gap (step H input) := by
  apply ((GraphTables.semantics (step H input).val).le_gap_iff _).mpr
  intro labeling
  rw [Fintype.card_fin]
  exact build_count_gap H certificate input labeling

end IndependentSetsGames.Foundations.PCP.RoundTableGap

namespace IndependentSetsGames.Foundations.PCP.TableGapReduction

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

end IndependentSetsGames.Foundations.PCP.TableGapReduction

end OAI
