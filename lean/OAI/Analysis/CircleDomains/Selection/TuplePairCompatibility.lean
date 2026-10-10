import OAI.Analysis.CircleDomains.Selection.FiniteTupleCompatibility
import OAI.Analysis.CircleDomains.Probability.TupleProductNull
import OAI.Analysis.CircleDomains.Probability.CircleNullImage

namespace OAI

/-! Independent tuples satisfy every ordered compatibility test and have
no equal levels carrying the same label across the two tuples. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

variable {X : Type*} [TopologicalSpace X]

def TuplePairCompatible (H : ℕ → Set (UnitAddCircle × X)) (F : Set X)
    (q r : LevelTuple) : Prop :=
  (∀ i j, q.2.1 i = r.2.1 j → q.2.2 i ≠ r.2.2 j) ∧
  (∀ j (A : Finset (Fin (q.1 + 1))), (∀ k ∈ A, q.2.1 k < r.2.1 j) →
    ∀ x ∈ F, (r.2.2 j, x) ∈ H (r.2.1 j) →
      ¬ (connectedComponentIn (⋃ k ∈ A, {y | (q.2.2 k, y) ∈ H (q.2.1 k)}) x).Nontrivial) ∧
  (∀ i (A : Finset (Fin (r.1 + 1))), (∀ k ∈ A, r.2.1 k < q.2.1 i) →
    ∀ x ∈ F, (q.2.2 i, x) ∈ H (q.2.1 i) →
      ¬ (connectedComponentIn (⋃ k ∈ A, {y | (r.2.2 k, y) ∈ H (r.2.1 k)}) x).Nontrivial)

theorem ae_torus_pair_distinct {n m : ℕ} :
    ∀ᵐ p ∂((volume : Measure (Fin n → UnitAddCircle)).prod
      (volume : Measure (Fin m → UnitAddCircle))), ∀ i j, p.1 i ≠ p.2 j := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  have hd : ((volume : Measure UnitAddCircle).prod volume)
      {p : UnitAddCircle × UnitAddCircle | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply (isClosed_eq continuous_fst continuous_snd).measurableSet]
    have hz : (volume : Measure UnitAddCircle) {0} = 0 := by
      simpa only [image_singleton, AddCircle.coe_zero] using
        (volume_addCircle_image_eq_zero (A := {(0 : ℝ)}) (measure_singleton 0))
    simp [hz]
  have hp := (measurePreserving_eval (fun _ : Fin n => (volume : Measure UnitAddCircle)) i).prod
    (measurePreserving_eval (fun _ : Fin m => (volume : Measure UnitAddCircle)) j)
  have hgood : ∀ᵐ p ∂((volume : Measure UnitAddCircle).prod volume), p.1 ≠ p.2 := by
    rw [ae_iff]
    simpa only [not_not] using hd
  exact hp.quasiMeasurePreserving.ae hgood

theorem tupleReference_pair_incompatible_null
    (H : ℕ → Set (UnitAddCircle × X)) (F : Set X)
    (hP : OrderedLevelNullCompatibility H F) (ω : TupleType → ℝ≥0∞) :
    ((tupleReference ω).prod (tupleReference ω))
      {p | ¬ TuplePairCompatible H F p.1 p.2} = 0 := by
  apply tupleReference_product_null
  intro i j
  have hleft := ae_finite_tuple_ordered_compatibility H F hP i.2 j.2
  have hright := Measure.measurePreserving_swap.quasiMeasurePreserving.ae
    (ae_finite_tuple_ordered_compatibility H F hP j.2 i.2)
  have hall : ∀ᵐ p ∂((volume : Measure (Fin (i.1 + 1) → UnitAddCircle)).prod
      (volume : Measure (Fin (j.1 + 1) → UnitAddCircle))),
      TuplePairCompatible H F (tupleFiber i p.1) (tupleFiber j p.2) := by
    filter_upwards [ae_torus_pair_distinct, hleft, hright] with p hp hl hr
    exact ⟨fun a b _ => hp a b, hl, hr⟩
  exact ae_iff.mp hall

end CircleDomainRigidity

end

end OAI
