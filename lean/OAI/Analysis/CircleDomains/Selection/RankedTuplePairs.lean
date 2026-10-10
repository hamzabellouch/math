import OAI.Analysis.CircleDomains.Selection.RankedTupleCompatibility
import OAI.Analysis.CircleDomains.Selection.TuplePairCompatibility

namespace OAI

/-! Independent tuple null sets with the inherited coordinate order. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩
variable {X : Type*} [TopologicalSpace X]

def RankedTuplePairCompatible {L : Type*} [LT L] (rank : ℕ → L) (H : ℕ → Set (UnitAddCircle × X)) (F : Set X)
    (q r : LevelTuple) : Prop :=
  (∀ i j, q.2.1 i = r.2.1 j → q.2.2 i ≠ r.2.2 j) ∧
  (∀ j (A : Finset (Fin (q.1 + 1))), (∀ k ∈ A, rank (q.2.1 k) < rank (r.2.1 j)) →
    ∀ x ∈ F, (r.2.2 j, x) ∈ H (r.2.1 j) →
      ¬ (connectedComponentIn (⋃ k ∈ A, {y | (q.2.2 k, y) ∈ H (q.2.1 k)}) x).Nontrivial) ∧
  (∀ i (A : Finset (Fin (r.1 + 1))), (∀ k ∈ A, rank (r.2.1 k) < rank (q.2.1 i)) →
    ∀ x ∈ F, (q.2.2 i, x) ∈ H (q.2.1 i) →
      ¬ (connectedComponentIn (⋃ k ∈ A, {y | (r.2.2 k, y) ∈ H (r.2.1 k)}) x).Nontrivial)

theorem tupleReference_ranked_pair_incompatible_null
    {L : Type*} [LinearOrder L] (rank : ℕ → L)
    (H : ℕ → Set (UnitAddCircle × X)) (F : Set X)
    (hP : RankedLevelNullCompatibility rank H F) (ω : TupleType → ℝ≥0∞) :
    ((tupleReference ω).prod (tupleReference ω))
      {p | ¬ RankedTuplePairCompatible rank H F p.1 p.2} = 0 := by
  apply tupleReference_product_null
  intro i j
  have hleft := ae_ranked_finite_tuple_ordered_compatibility rank H F hP i.2 j.2
  have hright := Measure.measurePreserving_swap.quasiMeasurePreserving.ae
    (ae_ranked_finite_tuple_ordered_compatibility rank H F hP j.2 i.2)
  have hall : ∀ᵐ p ∂((volume : Measure (Fin (i.1 + 1) → UnitAddCircle)).prod
      (volume : Measure (Fin (j.1 + 1) → UnitAddCircle))),
      RankedTuplePairCompatible rank H F (tupleFiber i p.1) (tupleFiber j p.2) := by
    filter_upwards [ae_torus_pair_distinct, hleft, hright] with p hp hl hr
    exact ⟨fun a b _ => hp a b, hl, hr⟩
  exact ae_iff.mp hall


end CircleDomainRigidity

end

end OAI
