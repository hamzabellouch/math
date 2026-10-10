import OAI.Analysis.CircleDomains.Selection.SparseBaseCodes
import OAI.Analysis.CircleDomains.Probability.SparseTupleMeasure
import OAI.Analysis.CircleDomains.Selection.TupleExclusions
import OAI.Analysis.CircleDomains.Selection.CodeConstraints

namespace OAI

/-! The auxiliary tuple cost can be removed from an admissible metric's
lower bound. This is the retagging step in Section 4 of the manuscript. -/

open Set MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)]

def nonTupleCost (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (Γ : BasePathCode d) (h : PathCostSpace Y D → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ y, h (costPhysical y) ∂baseCodeOccupation d Γ) +
    ∑' s, (c s * preterminalVisitCount Γ.val.1 (p s)) * h (costAtomic s)

theorem pathCostIntegral_sparse (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (Γ : BasePathCode d) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h)
    (e : ℕ ↪ ℕ) :
    (∫⁻ z, h z ∂pathCostMeasure d p c (sparseBaseCode d e Γ)) =
      nonTupleCost d p c Γ h +
        ∫⁻ t, h (costTuple t) ∂weightedTupleMeasure (sparseTags e Γ.val.2) := by
  rw [lintegral_pathCostMeasure d p c _ h hh, baseCodeOccupation_sparse]
  rfl

theorem exists_endpointCode_small_tuple (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X)
    (Γ : BasePathCode d) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h)
    (hΓ : EndpointCode d ν (tupleInfiniteExclusions (h ∘ costTuple)) Γ.val)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ,
      EndpointCode d ν (tupleInfiniteExclusions (h ∘ costTuple))
        (sparseBaseCode d e Γ).val ∧
      (∫⁻ z, h z ∂pathCostMeasure d p c (sparseBaseCode d e Γ)) ≤
        nonTupleCost d p c Γ h + ε := by
  obtain ⟨e, he⟩ := exists_sparse_tuple_cost_le Γ.val.2 (h ∘ costTuple)
    (tagRules_slotIntegral_finite (hh.comp measurable_costTuple) hΓ.1.2.1) hε
  refine ⟨e, endpointCode_sparse d ν _ e hΓ, ?_⟩
  rw [pathCostIntegral_sparse d p c Γ h hh]
  exact add_le_add le_rfl he

/-- Admissibility for the finite coding-measure family, with the prescribed
residual-image null constraint but without any tuple exclusions. -/
def CostAdmissible (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (ν : Measure X) (h : PathCostSpace Y D → ℝ≥0∞) : Prop :=
  ∀ Γ : BasePathCode d, pathCostMeasure d p c Γ univ < ∞ →
    ν (residualImage d.dust Γ.val) = 0 → 1 ≤ ∫⁻ z, h z ∂pathCostMeasure d p c Γ

theorem nonTupleCost_ge_one_of_admissible (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X)
    (Γ : BasePathCode d) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h)
    (hΓ : EndpointCode d ν (tupleInfiniteExclusions (h ∘ costTuple)) Γ.val)
    (hfinite : pathCostMeasure d p c Γ univ < ∞)
    (hadm : CostAdmissible d p c ν h) : 1 ≤ nonTupleCost d p c Γ h := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨e, he, hcost⟩ := exists_endpointCode_small_tuple d p c ν Γ h hh
    hΓ (ENNReal.coe_pos.mpr hε)
  exact (hadm (sparseBaseCode d e Γ)
    ((pathCostMeasure_sparse_finite_iff d p c e Γ).mpr hfinite) he.1.2.2.2.2).trans hcost

end CircleDomainRigidity

end

end OAI
