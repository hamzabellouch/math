import OAI.Computability.PerfectCompleteness.Machines.HierarchicalLowerMatrixInput
import OAI.Computability.PerfectCompleteness.Reduction.FixedRows

namespace OAI

section

namespace PerfectCompleteness.HierarchicalLowerInverse

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

local instance lowerHFintype (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) := Fintype.ofFinite _

abbrev Answer (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :=
  HierarchicalDecoderTables.Answer slots upper lowerLevel d

local instance answerFintype (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (Answer slots upper lowerLevel d) :=
  HierarchicalAllDecoderTables.answerFintype slots upper lowerLevel d

local instance upperDualFintype : Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  HierarchicalAllDecoderTables.upperDualFintype slots upper

def matrixTable {r : Nat}
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (table : HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel r →
      Option (Answer slots upper lowerLevel d)) :
    HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d →
      Option (Answer slots upper lowerLevel d) :=
  fun X => table (HierarchicalLowerMatrixInput.input slots upper lowerLevel
    background d upperMatrix A X)

variable (hbranch : ∀ k < n, 0 < branch k)

theorem matrixTable_tested {r s : Nat}
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (table : HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel r →
      Option (Answer slots upper lowerLevel d))
    (hvalid : DecoderTableAdmissibility.Admissible
      (HierarchicalAllDecoderTables.RowValid slots upper lowerLevel hbranch r d s) table)
    (X : HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d)
    (z : Answer slots upper lowerLevel d)
    (hz : matrixTable slots upper lowerLevel background d upperMatrix A table X = some z) :
    (LowerAffineSliceRank.testedGram
      (FunctionSpaceLowerRank.matrixForm
        (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (OddListExtraction.multiplicationForm
          (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) z)) X).rank ≤ 1 := by
  have h := hvalid
    (HierarchicalLowerMatrixInput.input slots upper lowerLevel background d upperMatrix A X)
    z hz
  have ht := h.2.1
  simpa only [HierarchicalLowerMatrixInput.input_testedMatrix] using ht

theorem matrixTable_high_rank {r s : Nat}
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (table : HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel r →
      Option (Answer slots upper lowerLevel d))
    (hvalid : DecoderTableAdmissibility.Admissible
      (HierarchicalAllDecoderTables.RowValid slots upper lowerLevel hbranch r d s) table)
    (X : HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d)
    (z : Answer slots upper lowerLevel d)
    (hz : matrixTable slots upper lowerLevel background d upperMatrix A table X = some z) :
    s < Module.finrank F2 (LinearMap.range
      (FunctionSpaceLowerRank.matrixForm
        (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (OddListExtraction.multiplicationForm
          (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) z))) := by
  rw [FunctionSpaceLowerRank.matrixForm_rank]
  exact (hvalid
    (HierarchicalLowerMatrixInput.input slots upper lowerLevel background d upperMatrix A X)
    z hz).2.2

theorem matrixTable_agreement_lt {r s m adviceRows : Nat}
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
    (table : HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel adviceRows →
      Option (Answer slots upper lowerLevel d))
    (hvalid : DecoderTableAdmissibility.Admissible
      (HierarchicalAllDecoderTables.RowValid slots upper lowerLevel hbranch adviceRows d s) table)
    (ρ η : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (hrows : 2 * m + r ≤ rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))
    (herror : (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) ≤ ρ) :
    PartialTableInverse.nonzeroAgreement
      (matrixTable slots upper lowerLevel background d upperMatrix A table) < η := by
  let f := matrixTable slots upper lowerLevel background d upperMatrix A table
  let form := fun z : Answer slots upper lowerLevel d =>
    FunctionSpaceLowerRank.matrixForm
      (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
      (OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) z)
  have tested : ∀ X z, f X = some z → (LowerAffineSliceRank.testedGram (form z) X).rank ≤ 1 :=
    fun X z hz => matrixTable_tested slots upper lowerLevel background hbranch
      d upperMatrix A table hvalid X z hz
  have high : ∀ X z, f X = some z → s < Module.finrank F2 (LinearMap.range (form z)) :=
    fun X z hz => matrixTable_high_rank slots upper lowerLevel background hbranch
      d upperMatrix A table hvalid X z hz
  have h := LowerAffineSliceRank.high_rank_agreement_lt f form tested r s ρ η
    hm hρ hρ1 hconstants hrows herror
  have herase : MatrixErasure.erase f (fun X => ∃ z, f X = some z ∧
      Module.finrank F2 (LinearMap.range (form z)) ≤ s) = f := by
    funext X
    apply MatrixErasure.erase_eq_of_not
    rintro ⟨z, hz, hrank⟩
    exact (not_le_of_gt (high X z hz)) hrank
  rw [herase] at h
  exact h

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel bg → Prop)

include hbranch σ useful

theorem supported_matrixTable_agreement_lt {r s m adviceRows : Nat}
    (decoderDensity : ℝ) (hdecoderDensity : 0 < decoderDensity)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
    (table : HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel adviceRows →
      Option (Answer slots upper lowerLevel d))
    (hsupport : (HierarchicalAllDecoderTables.tableLaw slots upper lowerLevel hbranch σ useful
      adviceRows decoderDensity d s).weight table ≠ 0)
    (ρ η : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (hrows : 2 * m + r ≤ rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))
    (herror : (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) ≤ ρ) :
    PartialTableInverse.nonzeroAgreement
      (matrixTable slots upper lowerLevel background d upperMatrix A table) < η := by
  exact matrixTable_agreement_lt slots upper lowerLevel background hbranch
    d upperMatrix A table
    (HierarchicalAllDecoderTables.supported_table_valid slots upper lowerLevel hbranch σ useful
      adviceRows decoderDensity hdecoderDensity d s table hsupport)
    ρ η hm hρ hρ1 hconstants hrows herror

theorem mean_matrixTable_agreement_le {r s m adviceRows : Nat}
    (decoderDensity : ℝ) (hdecoderDensity : 0 < decoderDensity)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
    (ρ η : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (hrows : 2 * m + r ≤ rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))
    (herror : (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) ≤ ρ) :
    (HierarchicalAllDecoderTables.tableLaw slots upper lowerLevel hbranch σ useful
      adviceRows decoderDensity d s).expectation
      (fun table => PartialTableInverse.nonzeroAgreement
        (matrixTable slots upper lowerLevel background d upperMatrix A table)) ≤ η := by
  apply DecoderTableAdmissibility.expectation_le_of_support
  intro table hsupport
  exact (supported_matrixTable_agreement_lt slots upper lowerLevel background hbranch
    σ useful decoderDensity hdecoderDensity d upperMatrix A table hsupport
    ρ η hm hρ hρ1 hconstants hrows herror).le

theorem supported_upper_matrixTable_agreement_lt {r s m adviceRows : Nat}
    (decoderDensity : ℝ) (hdecoderDensity : 0 < decoderDensity)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
    (table : HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel adviceRows →
      HierarchicalAllDecoderTables.UpperAnswer slots upper)
    (hsupport : (HierarchicalAllDecoderTables.upperTableLaw slots upper lowerLevel σ useful
      adviceRows decoderDensity).weight table ≠ 0)
    (ρ η : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (hrows : 2 * m + r ≤ rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))
    (herror : (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) ≤ ρ) :
    PartialTableInverse.nonzeroAgreement
      (matrixTable slots upper lowerLevel background d upperMatrix A
        (HierarchicalAllDecoderTables.decodeTable slots upper lowerLevel hbranch adviceRows d s table)) < η := by
  exact matrixTable_agreement_lt slots upper lowerLevel background hbranch
    d upperMatrix A
    (HierarchicalAllDecoderTables.decodeTable slots upper lowerLevel hbranch adviceRows d s table)
    (HierarchicalAllDecoderTables.decoded_supported_table_valid slots upper lowerLevel hbranch
      σ useful adviceRows decoderDensity hdecoderDensity table hsupport d s)
    ρ η hm hρ hρ1 hconstants hrows herror

end
end PerfectCompleteness.HierarchicalLowerInverse

end

section

namespace PerfectCompleteness.HierarchicalFixedLowerInverse

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ) (hδ : 0 < δ)
  {branch : Nat → Nat} {t : Nat}
  (slots : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (upper : Nodes branch plan.depth) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background
    (rows := FixedRows.rows plan) slots upper)

local instance lowerHFintype (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) := Fintype.ofFinite _

local instance upperDualFintype : Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  HierarchicalAllDecoderTables.upperDualFintype slots upper

variable (hbranch : ∀ k < plan.depth, 0 < branch k)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (useful : (bg : HierarchicalMatrixTable.Background
      (rows := FixedRows.rows plan) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel bg → Prop)

include hbranch σ useful

theorem supported_upper_matrixTable_agreement_lt {adviceRows : Nat}
    (decoderDensity : ℝ) (hdecoderDensity : 0 < decoderDensity)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix
      (rows := FixedRows.rows plan) slots upper)
    (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) adviceRows)
    (table : HierarchicalAllDecoderTables.Input
      (rows := FixedRows.rows plan) slots upper lowerLevel adviceRows →
        HierarchicalAllDecoderTables.UpperAnswer slots upper)
    (hsupport : (HierarchicalAllDecoderTables.upperTableLaw slots upper lowerLevel σ useful
      adviceRows decoderDensity).weight table ≠ 0) :
    PartialTableInverse.nonzeroAgreement
      (HierarchicalLowerInverse.matrixTable slots upper lowerLevel background d upperMatrix A
        (HierarchicalAllDecoderTables.decodeTable slots upper lowerLevel hbranch adviceRows d
          (FixedRows.cutoff plan hδ) table)) <
      UpperParameterScalars.gamma (InitialParameters.useful δ) plan.density
        (InitialParameters.inverse δ) plan.order
        (FixedRows.rows plan (Nodes.height upper)) ^ 2 / 8 := by
  let lower := DescendingRows.lowerChoice (InitialParameters.useful_pos hδ)
    plan.density_pos (InitialParameters.inverse_pos hδ) plan.order
    (FixedRows.rows plan (Nodes.height upper))
  have hheight : Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d) =
      lowerLevel :=
    (RelativeDescendantProducts.relativeNode_height upper d.val.val).trans d.property
  have hproper : lowerLevel < Nodes.height upper := by
    rw [← hheight]
    exact (RelativeDescendantProducts.descendantIndex_below upper d.val).height_lt
  have hminimum : lower.minimumRows ≤ FixedRows.rows plan lowerLevel :=
    FixedRows.lower_row_requirement plan hδ hproper (Nodes.height_le upper)
  have hrows : 2 * lower.crossSize + lower.order ≤
      FixedRows.rows plan (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)) := by
    rw [hheight]
    exact lower.row_bound _ hminimum
  have hcutoff : lower.cutoff ≤ FixedRows.cutoff plan hδ := by
    simpa only [lower, FixedRows.rows, FixedRows.cutoff] using
      DescendingRows.tree_cutoff_le_common (InitialParameters.useful_pos hδ)
        plan.density_pos (InitialParameters.inverse_pos hδ) plan.order plan.depth
        plan.rootFirstRows (Nat.zero_lt_of_lt hproper) (Nodes.height_le upper)
  exact HierarchicalLowerInverse.supported_upper_matrixTable_agreement_lt
    (r := lower.order) (s := FixedRows.cutoff plan hδ) (m := lower.crossSize)
    slots upper lowerLevel background hbranch σ useful decoderDensity hdecoderDensity
    d upperMatrix A table hsupport lower.density _ lower.cross_pos lower.density_pos
    lower.density_lt_one lower.spectral hrows (lower.error_bound _ hcutoff).le

end
end PerfectCompleteness.HierarchicalFixedLowerInverse

end

end OAI
