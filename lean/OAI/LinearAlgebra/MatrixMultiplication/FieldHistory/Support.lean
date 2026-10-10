import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Counts
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.HistorySupport
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CanonicalCW
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMaskMargins

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistorySupport

open AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem population_dilation {K : ℕ} (allocation : Allocation) (m : ℕ) (h : History K) :
    population allocation m h = m * population allocation 1 h := by
  simp only [population, AllFieldPopulationCounts.count, one_mul]

theorem branchPopulation_dilation {K : ℕ} (allocation : Allocation) (m : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    branchPopulation allocation m w b = m * branchPopulation allocation 1 w b := by
  simp only [branchPopulation, population, AllFieldPopulationCounts.count, one_mul]

theorem jointCounts_dilation {K : ℕ} (allocation : Allocation) (m : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    jointCounts allocation m w u = m * jointCounts allocation 1 w u := by
  simp only [jointCounts, shapeCounts, branchPopulation, population,
    AllFieldPopulationCounts.count, one_mul, Finset.mul_sum, mul_ite, mul_zero]

theorem activeCounts_dilation {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (h : Active K tick) (u : JointPopulation.Shape) :
    activeCounts allocation m h u = m * activeCounts allocation 1 h u :=
  jointCounts_dilation allocation m h.val u

theorem activeCounts_pos_iff {K tick m : ℕ} (allocation : Allocation) (hm : 0 < m)
    (h : Active K tick) (u : JointPopulation.Shape) :
    0 < activeCounts allocation m h u ↔ 0 < activeCounts allocation 1 h u := by
  rw [activeCounts_dilation]
  exact Nat.mul_pos_iff_of_pos_left hm

theorem dilation_le_activeCounts {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (h : Active K tick) (u : JointPopulation.Shape)
    (hpos : 0 < activeCounts allocation 1 h u) : m ≤ activeCounts allocation m h u := by
  rw [activeCounts_dilation]
  calc
    m = m * 1 := (Nat.mul_one m).symm
    _ ≤ m * activeCounts allocation 1 h u := Nat.mul_le_mul_left m hpos

theorem two_le_activeCounts {K tick m : ℕ} (allocation : Allocation) (hm : 2 ≤ m)
    (h : Active K tick) (u : JointPopulation.Shape)
    (hpos : 0 < activeCounts allocation 1 h u) : 2 ≤ activeCounts allocation m h u :=
  hm.trans (dilation_le_activeCounts allocation m h u hpos)

theorem totalLength_dilation {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (l r : Active K tick → ℕ) :
    HistorySupport.totalLength (JointPopulation.Positions (activeCounts allocation m)) l r =
      m * HistorySupport.totalLength (JointPopulation.Positions (activeCounts allocation 1)) l r := by
  simp only [HistorySupport.totalLength, JointPopulation.Positions, Fintype.card_fin,
    activeCounts_dilation allocation m, ← Finset.mul_sum, Nat.mul_assoc]

def fixedBaseLength {K tick : ℕ} (allocation : Allocation) : ℕ :=
  HistorySupport.totalLength
    (JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation 1))
    activeHalfLength activeHalfLength

def supportRate {K tick : ℕ} (allocation : Allocation) : ℝ :=
  RecoverySupport.cw5SupportRate (fixedBaseLength (K := K) (tick := tick) allocation)

theorem supportRate_pos {K tick : ℕ} (allocation : Allocation) :
    0 < supportRate (K := K) (tick := tick) allocation :=
  RecoverySupport.cw5SupportRate_pos _

abbrev ActiveRawPairs {K tick : ℕ} (allocation : Allocation) (m : ℕ) :=
  JointCanonicalization.RawPairs (activeCounts (K := K) (tick := tick) allocation m)
    (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength)

theorem raw_support_card_le_exp {K tick : ℕ} {F : Type*} [Zero F]
    (allocation : Allocation) (m : ℕ)
    (Q : ActiveRawPairs (K := K) (tick := tick) allocation m →
      ActiveRawPairs (K := K) (tick := tick) allocation m →
      ActiveRawPairs (K := K) (tick := tick) allocation m → F) :
    ((RecoverySupport.support Q).card : ℝ) ≤
      Real.exp (supportRate (K := K) (tick := tick) allocation * m) := by
  apply HistorySupport.cw5_support_card_le_exp
    (JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation m))
    activeHalfLength activeHalfLength Q (fixedBaseLength (K := K) (tick := tick) allocation) m
  rw [totalLength_dilation]
  exact le_of_eq (Nat.mul_comm _ _)

abbrev ActiveClass (K tick : ℕ) := Active K tick × JointPopulation.Shape

def selectedBaseCount {K tick : ℕ} (allocation : Allocation)
    (D : Finset (ActiveClass K tick)) : ℕ :=
  ∑ c ∈ D, activeCounts allocation 1 c.1 c.2

def selectedBasePopulation {K tick : ℕ} (allocation : Allocation)
    (D : Finset (ActiveClass K tick)) : ℝ := (selectedBaseCount allocation D : ℝ)

abbrev selectedPositions {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (D : Finset (ActiveClass K tick)) (c : D) :=
  JointCanonicalization.ClassPositions (activeCounts allocation m) c.val

theorem selected_count_dilation {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (D : Finset (ActiveClass K tick)) :
    (∑ c ∈ D, activeCounts allocation m c.1 c.2) = m * selectedBaseCount allocation D := by
  simp only [selectedBaseCount, activeCounts_dilation allocation m, Finset.mul_sum]

theorem selectedBaseCount_pos {K tick : ℕ} (allocation : Allocation)
    (D : Finset (ActiveClass K tick)) (hD : D.Nonempty)
    (hpos : ∀ c ∈ D, 0 < activeCounts allocation 1 c.1 c.2) :
    0 < selectedBaseCount allocation D :=
  Finset.sum_pos hpos hD

theorem selectedBasePopulation_pos {K tick : ℕ} (allocation : Allocation)
    (D : Finset (ActiveClass K tick)) (hD : D.Nonempty)
    (hpos : ∀ c ∈ D, 0 < activeCounts allocation 1 c.1 c.2) :
    0 < selectedBasePopulation allocation D := by
  unfold selectedBasePopulation
  exact_mod_cast selectedBaseCount_pos allocation D hD hpos

theorem selected_populationSize {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (D : Finset (ActiveClass K tick)) :
    PermutationMatching.populationSize (selectedPositions allocation m D) =
      selectedBasePopulation allocation D * (m : ℝ) := by
  simp only [PermutationMatching.populationSize, selectedPositions,
    JointCanonicalization.ClassPositions, Fintype.card_fin]
  rw [Finset.sum_coe_sort D
    (fun c : ActiveClass K tick => (activeCounts allocation m c.1 c.2 : ℝ))]
  simp only [activeCounts_dilation allocation m, Nat.cast_mul, ← Finset.mul_sum,
    selectedBasePopulation, selectedBaseCount, Nat.cast_sum]
  exact mul_comm _ _

theorem selected_two_le {K tick m : ℕ} (allocation : Allocation) (hm : 2 ≤ m)
    (D : Finset (ActiveClass K tick))
    (hpos : ∀ c ∈ D, 0 < activeCounts allocation 1 c.1 c.2) (c : D) :
    2 ≤ Fintype.card (selectedPositions allocation m D c) := by
  simpa only [selectedPositions, JointCanonicalization.ClassPositions, Fintype.card_fin] using
    two_le_activeCounts allocation hm c.val.1 c.val.2 (hpos c.val c.property)

theorem selected_classWeight_formula {K tick m : ℕ} (allocation : Allocation)
    (hm : 0 < m) (D : Finset (ActiveClass K tick)) (c : D) :
    PermutationMatching.classWeight (selectedPositions allocation m D) c =
      (activeCounts allocation 1 c.val.1 c.val.2 : ℝ) / selectedBasePopulation allocation D := by
  rw [PermutationMatching.classWeight, selected_populationSize]
  simp only [selectedPositions, JointCanonicalization.ClassPositions, Fintype.card_fin,
    activeCounts_dilation allocation m, Nat.cast_mul]
  rw [mul_comm (selectedBasePopulation allocation D) (m : ℝ)]
  exact mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))

theorem selected_classWeight_eq_one {K tick m : ℕ} (allocation : Allocation)
    (hm : 0 < m) (D : Finset (ActiveClass K tick)) (c : D) :
    PermutationMatching.classWeight (selectedPositions allocation m D) c =
      PermutationMatching.classWeight (selectedPositions allocation 1 D) c :=
  (selected_classWeight_formula allocation hm D c).trans
    (selected_classWeight_formula allocation (by decide : 0 < (1 : ℕ)) D c).symm

theorem selected_classProductMixture_eq_one {K tick m : ℕ} (allocation : Allocation)
    (hm : 0 < m) (D : Finset (ActiveClass K tick)) (left right : D → ℝ) :
    PermutationMatching.classProductMixture (selectedPositions allocation m D) left right =
      PermutationMatching.classProductMixture (selectedPositions allocation 1 D) left right := by
  unfold PermutationMatching.classProductMixture
  apply Finset.sum_congr rfl
  intro c _
  rw [selected_classWeight_eq_one allocation hm D c]

theorem work_source_amount_pos {K : ℕ} (allocation : Allocation) (w : PlacedWork K) :
    0 < amount allocation (w.1.source, w.2) := by
  rcases w with ⟨w, phi⟩
  unfold amount
  apply div_pos _ (by norm_num)
  cases w with
  | stageA h => exact initialAmount_pos h.val
  | stageB h => exact aAmount_pos h.val
  | stageC h => exact partAmount_pos allocation h

theorem work_source_population_pos {K m : ℕ} (allocation : Allocation) (hm : 0 < m)
    (w : PlacedWork K) : 0 < population allocation m (w.1.source, w.2) :=
  (AllFieldPopulationCounts.count_pos_iff (amount allocation) (amount_nonneg allocation)
    hm (w.1.source, w.2)).2 (work_source_amount_pos allocation w)

def positiveClasses {K tick : ℕ} (allocation : Allocation) (h : Active K tick) :
    Finset (ActiveClass K tick) :=
  Finset.univ.filter fun c => c.1 = h ∧ 0 < activeCounts allocation 1 c.1 c.2

theorem positiveClasses_positive {K tick : ℕ} (allocation : Allocation) (h : Active K tick)
    (c : ActiveClass K tick) (hc : c ∈ positiveClasses allocation h) :
    0 < activeCounts allocation 1 c.1 c.2 := (Finset.mem_filter.mp hc).2.2

theorem positiveClasses_baseCount {K tick : ℕ} (allocation : Allocation) (h : Active K tick) :
    selectedBaseCount allocation (positiveClasses allocation h) =
      population allocation 1 (h.val.1.source, h.val.2) := by
  have hkeep (n : ℕ) : (if 0 < n then n else 0) = n := by
    split_ifs <;> omega
  calc
    selectedBaseCount allocation (positiveClasses allocation h) =
        ∑ u, activeCounts allocation 1 h u := by
      simp [selectedBaseCount, positiveClasses, Finset.sum_filter, ite_and, hkeep,
        Fintype.sum_prod_type]
    _ = population allocation 1 (h.val.1.source, h.val.2) :=
      jointCounts_sum allocation 1 h.val

theorem positiveClasses_basePopulation_pos {K tick : ℕ} (allocation : Allocation)
    (h : Active K tick) : 0 < selectedBasePopulation allocation (positiveClasses allocation h) := by
  unfold selectedBasePopulation
  rw [positiveClasses_baseCount]
  exact_mod_cast work_source_population_pos allocation (by decide : 0 < (1 : ℕ)) h.val

theorem positiveClasses_nonempty {K tick : ℕ} (allocation : Allocation) (h : Active K tick) :
    (positiveClasses allocation h).Nonempty := by
  by_contra hn
  have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
  have hp := positiveClasses_basePopulation_pos allocation h
  simp [selectedBasePopulation, selectedBaseCount, hempty] at hp

theorem positiveClasses_populationSize {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (h : Active K tick) :
    PermutationMatching.populationSize
      (selectedPositions allocation m (positiveClasses allocation h)) =
        (population allocation 1 (h.val.1.source, h.val.2) : ℝ) * m := by
  rw [selected_populationSize]
  simp only [selectedBasePopulation, positiveClasses_baseCount]

end MatrixMultiplication.AllFieldHistorySupport

end

end OAI
