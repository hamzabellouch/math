import OAI.Analysis.CircleDomains.Modulus.RetaggedCost
import OAI.Analysis.CircleDomains.Selection.PreterminalTolls

namespace OAI

/-! A positive perturbation of an admissible coding metric gives a genuine
physical-plus-preterminal cost lower bound on every allowed path. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D] [MeasurableSpace C(PathTime, X)]

def physicalAtomicCost (d : PathCodeData X Y) (p : D → X) (Γ : BasePathCode d)
    (g : Y → ℝ≥0∞) (m : D → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ y, g y ∂baseCodeOccupation d Γ) +
    ∑' s, m s * preterminalVisitCount Γ.val.1 (p s)

omit [TopologicalSpace D] [MeasurableSpace D] [BorelSpace D] in
theorem nonTupleCost_le_physicalAtomicCost (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (Γ : BasePathCode d)
    (h : PathCostSpace Y D → ℝ≥0∞) (g : Y → ℝ≥0∞) (m : D → ℝ≥0∞)
    (hg : ∀ y, h (costPhysical y) ≤ g y)
    (hm : ∀ s, c s * h (costAtomic s) ≤ m s) :
    nonTupleCost d p c Γ h ≤ physicalAtomicCost d p Γ g m := by
  apply add_le_add (lintegral_mono hg)
  apply ENNReal.tsum_le_tsum
  intro s
  calc
    (c s * preterminalVisitCount Γ.val.1 (p s)) * h (costAtomic s) =
        (c s * h (costAtomic s)) * preterminalVisitCount Γ.val.1 (p s) := by ac_rfl
    _ ≤ m s * preterminalVisitCount Γ.val.1 (p s) := mul_le_mul' (hm s) le_rfl

theorem finite_code_of_physicalAtomicCost (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (Γ : BasePathCode d)
    (g : Y → ℝ≥0∞) (m : D → ℝ≥0∞) {δ : ℝ≥0∞}
    (hδ : 0 < δ) (hm : ∀ s, δ * c s ≤ m s)
    (hcost : physicalAtomicCost d p Γ g m < ∞) :
    pathCostMeasure d p c Γ univ < ∞ := by
  rw [pathCostMeasure_finite_iff]
  apply finite_preterminal_sum_of_positive_tolls Γ.val.1 p hδ hm
  exact lt_of_le_of_lt le_add_self hcost

theorem physicalAtomicCost_ge_one (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X) (Γ : BasePathCode d)
    (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h)
    (hΓ : EndpointCode d ν (tupleInfiniteExclusions (h ∘ costTuple)) Γ.val)
    (hadm : CostAdmissible d p c ν h)
    (g : Y → ℝ≥0∞) (m : D → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ)
    (hg : ∀ y, h (costPhysical y) ≤ g y)
    (hm : ∀ s, c s * h (costAtomic s) ≤ m s)
    (hpos : ∀ s, δ * c s ≤ m s) :
    1 ≤ physicalAtomicCost d p Γ g m := by
  by_cases hfinite : physicalAtomicCost d p Γ g m < ∞
  · exact (nonTupleCost_ge_one_of_admissible d p c ν Γ h hh hΓ
      (finite_code_of_physicalAtomicCost d p c Γ g m hδ hpos hfinite) hadm).trans
      (nonTupleCost_le_physicalAtomicCost d p c Γ h g m hg hm)
  · rw [top_unique (not_lt.mp hfinite)]
    exact le_top

end CircleDomainRigidity

end

end OAI
