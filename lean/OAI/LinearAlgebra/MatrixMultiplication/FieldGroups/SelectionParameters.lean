import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.TargetRate
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ActiveCapacity

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupSelection

open MatrixMultiplication.Foundation AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldScheduledYield AllFieldNativeCapacity
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def nativeDegree (allocation : Allocation) (sigma : Placement) : ℝ :=
  max (orderNativeDegree (K := K) (tick := tick) allocation sigma 0)
    (max (orderNativeDegree (K := K) (tick := tick) allocation sigma 1)
      (orderNativeDegree (K := K) (tick := tick) allocation sigma 2))

theorem targetEntropy_eq (allocation : Allocation) (sigma : Placement) :
    AllFieldGroupTargetRate.groupEntropyRate (K := K) (tick := tick)
      (sigma := sigma) allocation =
      orderEntropyRate (K := K) (tick := tick) allocation sigma := rfl

theorem firstDegree_nonneg (allocation : Allocation) (sigma : Placement) :
    0 ≤ orderNativeDegree (K := K) (tick := tick) allocation sigma 0 := by
  apply Finset.sum_nonneg
  intro h _
  apply mul_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) (orderMass_nonneg allocation h)
  · rw [order_first_capacity h]
    exact sub_nonneg.mpr
      (JointOrdinaryPopulationSelection.sideMass_entropy_le (orderLaw h) (sigma 0))

theorem nativeDegree_nonneg (allocation : Allocation) (sigma : Placement) :
    0 ≤ nativeDegree (K := K) (tick := tick) allocation sigma :=
  (firstDegree_nonneg allocation sigma).trans (le_max_left _ _)

def nativeCapacity (allocation : Allocation) : ℝ :=
  (populationLength (K := K) allocation 1 : ℝ) *
    ((1 / 6 : ℝ) * Staggering.minCapacity
      (FiniteSchedule.tickCapacity K nativeLA nativeLB
        (nativeLC (fun i => (allocation.mass i : ℝ))) tick))

theorem targetEntropy_sub_degree (allocation : Allocation) (sigma : Placement) :
    AllFieldGroupTargetRate.groupEntropyRate (K := K) (tick := tick)
      (sigma := sigma) allocation - nativeDegree (K := K) (tick := tick) allocation sigma =
        nativeCapacity (K := K) (tick := tick) allocation :=
  order_entropy_sub_native_degree K tick allocation sigma

def selectionHashRate (allocation : Allocation) (sigma : Placement) (slack : ℝ) : ℝ :=
  nativeDegree (K := K) (tick := tick) allocation sigma + slack / 2

theorem selectionHashRate_nonneg (allocation : Allocation) (sigma : Placement)
    {slack : ℝ} (hslack : 0 < slack) :
    0 ≤ selectionHashRate (K := K) (tick := tick) allocation sigma slack := by
  unfold selectionHashRate
  linarith [nativeDegree_nonneg (K := K) (tick := tick) allocation sigma]

theorem selectionHashRate_gap (allocation : Allocation) (sigma : Placement)
    {slack : ℝ} (hslack : 0 < slack) :
    nativeDegree (K := K) (tick := tick) allocation sigma <
      selectionHashRate (K := K) (tick := tick) allocation sigma slack := by
  unfold selectionHashRate
  linarith

theorem selectionHashRate_window_gap (allocation : Allocation) (sigma : Placement)
    {slack : ℝ} (hslack : 0 < slack) :
    nativeDegree (K := K) (tick := tick) allocation sigma + slack / 4 <
      selectionHashRate (K := K) (tick := tick) allocation sigma slack := by
  unfold selectionHashRate
  linarith

theorem selection_exponent (allocation : Allocation) (sigma : Placement) (slack : ℝ) :
    AllFieldGroupTargetRate.groupEntropyRate (K := K) (tick := tick)
      (sigma := sigma) allocation -
        selectionHashRate (K := K) (tick := tick) allocation sigma slack - slack / 2 =
      nativeCapacity (K := K) (tick := tick) allocation - slack := by
  rw [selectionHashRate]
  linarith [targetEntropy_sub_degree (K := K) (tick := tick) allocation sigma]

end MatrixMultiplication.AllFieldGroupSelection

end

end OAI
