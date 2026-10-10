import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ActiveLaws
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CompatibilityScaling

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupTargetRate

open AllFieldHistory AllFieldActiveLaws MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} {sigma : Placement}

theorem source_unit_pos (allocation : Allocation) :
    0 < populationLength (K := K) allocation 1 :=
  AllFieldPopulationCounts.blockLength_pos (amount (K := K) allocation) (by decide)

theorem source_length_dilation (allocation : Allocation) (m : ℕ) :
    populationLength (K := K) allocation m =
      m * populationLength (K := K) allocation 1 :=
  populationLength_dilation allocation m

theorem orderCounts_dilation (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape) :
    orderCounts allocation m h u = m * orderCounts allocation 1 h u := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_mul, orderCounts_source_cast, orderCounts_source_cast,
    populationLength_dilation, Nat.cast_mul]
  ring

theorem orderCounts_dilation_fun (allocation : Allocation) (m : ℕ) :
    orderCounts (K := K) (tick := tick) (sigma := sigma) allocation m =
      fun h u => m * orderCounts allocation 1 h u := by
  funext h u
  exact orderCounts_dilation allocation m h u

theorem orderCounts_sum (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma) :
    (∑ u, orderCounts allocation m h u) =
      population allocation m (h.val.val.1.source, h.val.val.2) :=
  jointCounts_sum allocation m h.val.val

theorem baseSize_eq_population (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma) :
    JointCompatibilityScaling.baseSize (orderCounts allocation m) h =
      population allocation m (h.val.val.1.source, h.val.val.2) :=
  orderCounts_sum allocation m h

theorem baseSize_dilation (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma) :
    JointCompatibilityScaling.baseSize (orderCounts allocation m) h =
      m * JointCompatibilityScaling.baseSize (orderCounts allocation 1) h := by
  simp only [JointCompatibilityScaling.baseSize]
  simp_rw [orderCounts_dilation allocation m]
  exact (Finset.mul_sum Finset.univ _ m).symm

theorem baseSize_cast_real (allocation : Allocation)
    (h : ActiveOrder K tick sigma) :
    (JointCompatibilityScaling.baseSize (orderCounts allocation 1) h : ℝ) =
      (populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h := by
  rw [baseSize_eq_population, population_cast_real]
  rfl

theorem baseSize_pos (allocation : Allocation)
    (h : ActiveOrder K tick sigma) :
    0 < JointCompatibilityScaling.baseSize (orderCounts allocation 1) h := by
  rw [baseSize_eq_population]
  exact work_source_population_pos allocation (by decide) h.val.val

theorem base_empirical_eq (allocation : Allocation)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape) :
    (orderCounts allocation 1 h u : ℝ) /
      JointCompatibilityScaling.baseSize (orderCounts allocation 1) h =
        (orderLaw h).mass u := by
  rw [baseSize_eq_population]
  exact jointCounts_ratio allocation (by decide) h.val.val u

def groupEntropyRate (allocation : Allocation) : ℝ :=
  ∑ h : ActiveOrder K tick sigma,
    ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
      finiteEntropy (orderLaw h).mass

theorem groupEntropyRate_nonneg (allocation : Allocation) :
    0 ≤ groupEntropyRate (K := K) (tick := tick) (sigma := sigma) allocation := by
  apply Finset.sum_nonneg
  intro h _
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (orderMass_nonneg allocation h))
    (FiniteLaw.entropy_nonneg (orderLaw h))

theorem baseEntropy_eq_groupEntropyRate (allocation : Allocation) :
    JointCompatibilityScaling.baseEntropy
      (orderCounts (K := K) (tick := tick) (sigma := sigma) allocation 1) =
        groupEntropyRate (K := K) (tick := tick) (sigma := sigma) allocation := by
  simp only [JointCompatibilityScaling.baseEntropy, groupEntropyRate]
  simp only [base_empirical_eq]
  simp only [baseSize_cast_real]

theorem target_card_pos (allocation : Allocation) (m : ℕ) :
    0 < Fintype.card (JointPopulation.Target
      (orderCounts (K := K) (tick := tick) (sigma := sigma) allocation m)) :=
  Fintype.card_pos_iff.mpr (JointPopulation.target_nonempty _)

theorem tendsto_log_target_card_div (allocation : Allocation) :
    Tendsto (fun m : ℕ =>
      Real.log (Fintype.card (JointPopulation.Target
        (orderCounts (K := K) (tick := tick) (sigma := sigma) allocation m)) : ℝ) /
          (m : ℝ)) atTop
      (𝓝 (groupEntropyRate (K := K) (tick := tick) (sigma := sigma) allocation)) := by
  apply JointPopulationRates.tendsto_log_target_card_div_of_coordinate_rates
    (fun m => orderCounts allocation m)
    (fun h => (populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h)
    (fun h => (orderLaw h).mass)
  · intro h
    exact mul_nonneg (Nat.cast_nonneg _) (orderMass_nonneg allocation h)
  · intro h
    exact (orderLaw h).total
  · exact orderCounts_dilation_rate allocation

theorem tendsto_log_targetSet_card_div (allocation : Allocation) :
    Tendsto (fun m : ℕ =>
      Real.log ((JointPopulation.targetSet
        (orderCounts (K := K) (tick := tick) (sigma := sigma) allocation m)).card : ℝ) /
          (m : ℝ)) atTop
      (𝓝 (groupEntropyRate (K := K) (tick := tick) (sigma := sigma) allocation)) := by
  simpa only [JointPopulation.target_card, JointPopulation.targetSet_card] using
    tendsto_log_target_card_div (K := K) (tick := tick) (sigma := sigma) allocation

end MatrixMultiplication.AllFieldGroupTargetRate

end

end OAI
