import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Counts
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.HistorySupport

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem work_source_amount_pos {K : ℕ} (allocation : Allocation) (w : PlacedWork K) :
    0 < amount allocation (w.1.source, w.2) := by
  apply div_pos _ (by norm_num)
  cases w.1 with
  | stageA h => exact initialAmount_pos h.val
  | stageB h => exact aAmount_pos h.val
  | stageC h => exact partAmount_pos allocation h

theorem work_source_population_pos {K : ℕ} (allocation : Allocation) {dilation : ℕ}
    (hd : 0 < dilation) (w : PlacedWork K) :
    0 < population allocation dilation (w.1.source, w.2) :=
  (AllFieldPopulationCounts.count_pos_iff _ (amount_nonneg allocation) hd _).mpr
    (work_source_amount_pos allocation w)

abbrev PositiveBranch {K : ℕ} (allocation : Allocation) (w : PlacedWork K) :=
  {b : w.1.Branch // 0 < amount allocation (w.1.child b false, w.2)}

theorem branchPopulation_pos_iff {K : ℕ} (allocation : Allocation) {dilation : ℕ}
    (hd : 0 < dilation) (w : PlacedWork K) (b : w.1.Branch) :
    0 < branchPopulation allocation dilation w b ↔
      0 < amount allocation (w.1.child b false, w.2) :=
  AllFieldPopulationCounts.count_pos_iff _ (amount_nonneg allocation) hd _

theorem positive_branch_minimum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : PositiveBranch allocation w) :
    dilation ≤ branchPopulation allocation dilation w b.val :=
  AllFieldPopulationCounts.dilation_le_count _ (amount_nonneg allocation) dilation _ b.property

theorem positive_joint_class_minimum {K : ℕ} (allocation : Allocation) {dilation : ℕ}
    (hd : 0 < dilation) (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : 0 < jointCounts allocation dilation w u) : dilation ≤ jointCounts allocation dilation w u := by
  obtain ⟨b, rfl, hb⟩ := shapeCounts_positive _ _ u hu
  rw [jointCounts_at]
  exact positive_branch_minimum allocation dilation w
    ⟨b, (branchPopulation_pos_iff allocation hd w b).mp hb⟩

def activeLengthRate {K tick : ℕ} (allocation : Allocation) : ℚ :=
  ∑ h : Active K tick, amount allocation (h.val.1.source, h.val.2) *
    (2 * h.val.1.halfLength : ℕ)

def activePositions {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : Active K tick) : Type :=
  Fin (population allocation dilation (h.val.1.source, h.val.2))

instance {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) (h : Active K tick) :
    Fintype (activePositions allocation dilation h) := inferInstanceAs (Fintype (Fin _))

theorem active_totalLength_cast {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :
    (HistorySupport.totalLength (activePositions (K := K) (tick := tick) allocation dilation)
      activeHalfLength activeHalfLength : ℚ) =
      (populationLength (K := K) allocation dilation : ℚ) *
        activeLengthRate (K := K) (tick := tick) allocation := by
  simp only [HistorySupport.totalLength, Nat.cast_sum, Nat.cast_mul,
    activeHalfLength, activeLengthRate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hcard : Fintype.card (activePositions allocation dilation h) =
      population allocation dilation (h.val.1.source, h.val.2) := Fintype.card_fin _
  rw [hcard, population_cast]
  push_cast
  ring

def activeLengthBudget {K tick : ℕ} (allocation : Allocation) : ℕ :=
  Nat.ceil (activeLengthRate (K := K) (tick := tick) allocation)

theorem active_totalLength_le {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :
    HistorySupport.totalLength (activePositions (K := K) (tick := tick) allocation dilation)
      activeHalfLength activeHalfLength ≤
      activeLengthBudget (K := K) (tick := tick) allocation *
        populationLength (K := K) allocation dilation := by
  have h := active_totalLength_cast (K := K) (tick := tick) allocation dilation
  have hc : activeLengthRate (K := K) (tick := tick) allocation ≤
      (activeLengthBudget (K := K) (tick := tick) allocation : ℚ) := Nat.le_ceil _
  have hb := mul_le_mul_of_nonneg_left hc
    (Nat.cast_nonneg (populationLength (K := K) allocation dilation) :
      (0 : ℚ) ≤ populationLength (K := K) allocation dilation)
  rw [← h] at hb
  exact_mod_cast hb.trans_eq (mul_comm _ _)

theorem active_cw5_support_bound {F : Type*} [Zero F] {K tick : ℕ}
    (allocation : Allocation) (dilation : ℕ)
    (Q : HistorySupport.HistoryWords
      (activePositions (K := K) (tick := tick) allocation dilation)
      activeHalfLength activeHalfLength 7 →
      HistorySupport.HistoryWords
        (activePositions (K := K) (tick := tick) allocation dilation)
        activeHalfLength activeHalfLength 7 →
      HistorySupport.HistoryWords
        (activePositions (K := K) (tick := tick) allocation dilation)
        activeHalfLength activeHalfLength 7 → F) :
    ((RecoverySupport.support Q).card : ℝ) ≤
      Real.exp (RecoverySupport.cw5SupportRate
        (activeLengthBudget (K := K) (tick := tick) allocation) *
          (populationLength (K := K) allocation dilation : ℝ)) :=
  HistorySupport.cw5_support_card_le_exp _ _ _ Q _ _
    (active_totalLength_le allocation dilation)

end MatrixMultiplication.AllFieldHistory

end

end OAI
