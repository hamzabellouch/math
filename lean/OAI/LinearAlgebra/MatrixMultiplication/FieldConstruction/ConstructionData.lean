import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialChoice
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Iteration
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.FinishedWitness
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ConstructionRates

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldConstructionData

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ}

structure Data (allocation : Allocation) (dilation : ℕ) (width slack : ℝ) where
  initial : AllFieldInitialChoice.Choice (K := K) allocation dilation slack
  groups : AllFieldHistoryIteration.ScheduleChoices
    (K := K) allocation dilation width slack
  threshold : ∀ t : Fin (K + 2),
    AllFieldHistoryRecovery.minimumDilation (K := K) (tick := t.val) allocation width ≤ dilation

variable (allocation : Allocation) (dilation : ℕ) (width slack : ℝ)

abbrev Tags (data : Data (K := K) allocation dilation width slack) :=
  AllFieldHistoryIteration.Tags allocation dilation width slack
    (AllFieldInitialChoice.Tags allocation dilation slack data.initial) data.groups

instance tagsFintype (data : Data (K := K) allocation dilation width slack) :
    Fintype (Tags allocation dilation width slack data) := inferInstance

def execution (F : Type*) [Field F] (hwidth : 0 < width)
    (data : Data (K := K) allocation dilation width slack) :
    Execution (cwSource F K (populationLength (K := K) allocation dilation))
      (Tensor.directSum (fun _ : Tags allocation dilation width slack data =>
        stateTensor F (K := K) allocation dilation width (K + 2))) :=
  AllFieldHistoryIteration.execution allocation dilation width slack F hwidth
    data.threshold data.groups
    (AllFieldInitialChoice.execution allocation dilation slack data.initial F width)

theorem card_tags (data : Data (K := K) allocation dilation width slack) :
    Fintype.card (Tags allocation dilation width slack data) =
      Fintype.card (AllFieldConstructionRates.SelectedLabels
        (K := K) allocation slack dilation) := by
  rw [AllFieldHistoryIteration.card_tags, AllFieldInitialChoice.card_tags,
    AllFieldConstructionRates.card_selected]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  apply Finset.prod_congr rfl
  intro sigma _
  exact (AllFieldConstructionRates.groupCount_eq_native allocation slack dilation t sigma).symm

theorem execution_copies (F : Type*) [Field F] (hwidth : 0 < width)
    (data : Data (K := K) allocation dilation width slack) :
    Fintype.card (execution allocation dilation width slack F hwidth data).Copies =
      Fintype.card (AllFieldConstructionRates.Copies
        (K := K) allocation width dilation) := by
  rw [execution, AllFieldHistoryIteration.execution_copies,
    AllFieldInitialChoice.execution_copies, one_mul]
  simp only [AllFieldConstructionRates.Copies, Fintype.card_pi,
    InverseLinearRecovery.MaskRectangles, ExactRecovery.card_mask_rectangles, Fintype.card_fin]

theorem tags_pos
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation dilation width slack) :
    0 < Fintype.card (Tags allocation dilation width slack data) := by
  rw [card_tags]
  exact AllFieldConstructionRates.selected_pos allocation slack hslack dilation

variable {F : Type*} [Field F] (m : ℕ)

def witness (hm : 0 < m) (hwidth : 0 < width)
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K m) width slack) : AllFieldWitness F :=
  AllFieldFinishedWitness.witness allocation m hm hwidth.le
    (execution allocation (AllFieldTerminalRates.terminalDilation K m) width slack F hwidth data)
    (tags_pos allocation (AllFieldTerminalRates.terminalDilation K m) width slack hslack data)

@[simp] theorem witness_volume (hm : 0 < m) (hwidth : 0 < width)
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K m) width slack) :
    (witness (F := F) allocation width slack m hm hwidth hslack data).volume =
      AllFieldTerminalRates.terminalVolume (K := K) allocation m :=
  AllFieldFinishedWitness.witness_volume _ _ _ _ _ _

@[simp] theorem witness_multiplicity (hm : 0 < m) (hwidth : 0 < width)
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K m) width slack) :
    (witness (F := F) allocation width slack m hm hwidth hslack data).multiplicity =
      Fintype.card (AllFieldConstructionRates.SelectedLabels
        (K := K) allocation slack (AllFieldTerminalRates.terminalDilation K m)) := by
  change Fintype.card (Tags _ _ _ _ data) = _
  exact card_tags _ _ _ _ data

@[simp] theorem witness_rankBound (hm : 0 < m) (hwidth : 0 < width)
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K m) width slack) :
    (witness (F := F) allocation width slack m hm hwidth hslack data).rankBound =
      AllFieldSource.rankBudget
        (AllFieldConstructionRates.Copies (K := K) allocation width
          (AllFieldTerminalRates.terminalDilation K m)) K
        (AllFieldTerminalRates.terminalLength allocation K m) := by
  rw [witness]
  erw [AllFieldFinishedWitness.witness_rankBound]
  unfold AllFieldSource.rankBudget
  rw [execution_copies]

end MatrixMultiplication.AllFieldConstructionData

end

end OAI
