import OAI.Computability.PerfectCompleteness.Construction.AscendingBranchingLemmas
import OAI.Computability.PerfectCompleteness.Foundations.SourceOddListsLemmas
import OAI.Computability.PerfectCompleteness.Machines.PreprocessingMachineLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CompletionLemmas

namespace OAI

section

namespace PerfectCompleteness.FixedRows

open InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier

noncomputable section

structure Plan (δ : ℚ) where
  depth : Nat
  depth_ge : 2 ≤ depth
  depth_mass : 4 ≤ (depth : ℝ) * epsilon δ
  order : Nat
  order_pos : 1 ≤ order
  density : ℝ
  density_pos : 0 < density
  density_lt : density < 1
  spectral : MatrixLevelBridge.levelCutoffConstant order density +
    RankLevelFilter.node (order + 1) < inverse δ / 2
  rootFirstRows : Nat → Nat
  rows_order : ∀ k, order ≤ rootFirstRows k
  rows_pos : ∀ k, 1 ≤ rootFirstRows k
  rows_correction : ∀ k, 1 / (2 : ℝ) ^ (rootFirstRows k - order) <
    rhoPred (useful δ) density / 8
  repeatCount : Nat → Nat
  repeats_min : ∀ ℓ, 6 ≤ repeatCount ℓ
  repeats_error : ∀ ℓ, (7 / 8 : ℝ) ^ repeatCount ℓ ≤
    min (h order ℓ / 2) (tau (useful δ) density order ℓ ^ 2 / 2)
  lowerRequirements : ∀ (hδ : 0 < δ) k (i : Fin k),
    (DescendingRows.lowerChoice (useful_pos hδ) density_pos (inverse_pos hδ)
      order (rootFirstRows i.val)).minimumRows ≤ rootFirstRows k

theorem exists_plan {δ : ℚ} (hδ : 0 < δ) (hδ' : δ < 1) : Nonempty (Plan δ) := by
  obtain ⟨depth, r, hd, hmass, hr, α, hα, hα', hspectral⟩ :=
    exists_initial hδ hδ'
  obtain ⟨rows, hrows⟩ := DescendingRows.exists_rows
    (useful_pos hδ) hα (inverse_pos hδ) r 1
  have hreps : ∀ ℓ : Nat, ∃ R : Nat, 6 ≤ R ∧ (7 / 8 : ℝ) ^ R ≤
      min (h r ℓ / 2) (tau (useful δ) α r ℓ ^ 2 / 2) :=
    fun ℓ => exists_upper_repeats (useful_pos hδ) hα r ℓ
  choose repeats hrepeats using hreps
  exact ⟨{
    depth := depth
    depth_ge := hd
    depth_mass := hmass
    order := r
    order_pos := hr
    density := α
    density_pos := hα
    density_lt := hα'
    spectral := hspectral
    rootFirstRows := rows
    rows_order := fun k => (hrows k).2.1
    rows_pos := fun k => (hrows k).2.2.1
    rows_correction := fun k => (hrows k).2.2.2.1
    repeatCount := repeats
    repeats_min := fun ℓ => (hrepeats ℓ).1
    repeats_error := fun ℓ => (hrepeats ℓ).2
    lowerRequirements := fun _ k => (hrows k).2.2.2.2 }⟩

variable {δ : ℚ} (plan : Plan δ)

def rows : Nat → Nat := DescendingRows.treeRows plan.depth plan.rootFirstRows
def repeats : Nat → Nat := fun height => plan.repeatCount (rows plan height)

def cutoff (hδ : 0 < δ) : Nat :=
  DescendingRows.commonCutoff (useful_pos hδ) plan.density_pos (inverse_pos hδ)
    plan.order plan.depth plan.rootFirstRows

theorem cutoff_pos (hδ : 0 < δ) : 0 < cutoff plan hδ :=
  DescendingRows.commonCutoff_pos (useful_pos hδ) plan.density_pos (inverse_pos hδ)
    plan.order plan.depth plan.rootFirstRows

instance cutoff_neZero (hδ : 0 < δ) : NeZero (cutoff plan hδ) :=
  ⟨Nat.ne_of_gt (cutoff_pos plan hδ)⟩

def sourceLength (hδ : 0 < δ) : Nat :=
  SourceOddLists.repetitionLength PCPSource.sourceGap (cutoff plan hδ)
    PCPSource.sourceGap_pos PCPSource.sourceGap_le_one

theorem sourceLength_pos (hδ : 0 < δ) : 0 < sourceLength plan hδ :=
  SourceOddLists.repetitionLength_positive PCPSource.sourceGap (cutoff plan hδ)
    PCPSource.sourceGap_pos PCPSource.sourceGap_le_one

theorem source_oddList_value_le_half (hδ : 0 < δ)
    (input : List Bool) (unsat : ¬BinaryLanguage.language input) :
    (SourceOddLists.game (cutoff plan hδ)
      (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
      (sourceLength plan hδ)).value ≤ 1 / 2 :=
  SourceOddLists.value_le_half
    (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    PCPSource.sourceGap PCPSource.sourceGap_pos PCPSource.sourceGap_le_one
    (PCPSourceMachine.rawSource_clauseGap input unsat)

theorem lower_row_requirement (hδ : 0 < δ) {i j : Nat}
    (hij : i < j) (hj : j ≤ plan.depth) :
    (DescendingRows.lowerChoice (useful_pos hδ) plan.density_pos (inverse_pos hδ)
      plan.order (rows plan j)).minimumRows ≤ rows plan i :=
  DescendingRows.tree_pair_requirement (useful_pos hδ) plan.density_pos (inverse_pos hδ)
    plan.order plan.depth plan.rootFirstRows (plan.lowerRequirements hδ) hij hj

end
end PerfectCompleteness.FixedRows

end

end OAI
