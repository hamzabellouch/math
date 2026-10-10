import OAI.Analysis.CircleDomains.Rigidity.OrderedMaskedSelection
import OAI.Analysis.CircleDomains.Topology.GreedyOpenSelection
import OAI.Analysis.CircleDomains.Topology.MapDiskExclusion

namespace OAI

/-! Countable open selection retains every seed and the actual order of
later masked coordinates. Its cover assertion concerns every candidate
compatible with the final list; geometric availability is proved separately. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 def seededMaskedAllowed {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π) {T : Type*}
    (data : T → SelectableMaskedCoordinate d π) (A : Set T) (c : T) : Prop :=
  (data c).CompatibleWith (range seed ∪ data '' A)

 theorem seededMaskedAllowed_mono {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π) {T : Type*}
    (data : T → SelectableMaskedCoordinate d π) {A B : Set T} (hAB : A ⊆ B)
    {c : T} (h : seededMaskedAllowed seed data B c) : seededMaskedAllowed seed data A c :=
  h.mono (union_subset_union (Subset.refl _) (image_mono hAB))

 theorem exists_seeded_masked_selection
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π)
    (hzero : (seed 0).coordinate.graph = circleBandGraph d.quotientDomain (fun _ => 0))
    (hseed : ∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ k, (seed k).flags) (seed j).coordinate.graph
          (fun k => (seed k).coordinate.graph) labels) = 0)
    {T X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (data : T → SelectableMaskedCoordinate d π) (V : T → Set X) (hV : ∀ c, IsOpen (V c)) :
    ∃ (A : ℕ → Set T) (q : ℕ → Option T),
      A 0 = ∅ ∧ (∀ n, (A n).Finite) ∧ Monotone A ∧ (⋃ n, A n).Countable ∧
      (∀ n c, q n = some c ↔ c ∈ A (n + 1) \ A n) ∧
      (∀ n c, c ∈ A n ↔ ∃ k < n, q k = some c) ∧
      (∀ c, seededMaskedAllowed seed data (⋃ n, A n) c →
        V c ⊆ ⋃ t ∈ ⋃ n, A n, V t) ∧
      (∀ c ∈ ⋃ n, A n, ∃ j : ℕ ⊕ₗ ℕ, orderedSelectedCoordinates seed data q j = data c) ∧
      let D := orderedSelectedCoordinates seed data q
      ∀ (j : ℕ ⊕ₗ ℕ) (n : ℕ) (labels : Fin n → ℕ ⊕ₗ ℕ), (∀ i, labels i < j) →
        (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (d.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
            (fun k => (D k).coordinate.graph) labels) = 0 := by
  obtain ⟨A, hA0, hfin, hmono, hsingle, hnew, hcount, hcover⟩ :=
    exists_countable_open_selection V hV (seededMaskedAllowed seed data)
      (fun hAB c hc => ⟨c, seededMaskedAllowed_mono seed data hAB hc, Subset.rfl⟩)
  obtain ⟨q, hq, hpref⟩ := exists_ordered_selection_slots A hA0 hmono hsingle
  refine ⟨A, q, hA0, hfin, hmono, hcount, hq, hpref, hcover, ?_, ?_⟩
  · intro c hc
    obtain ⟨n, hn⟩ := mem_iUnion.mp hc
    obtain ⟨k, _, hk⟩ := (hpref n c).mp hn
    refine ⟨Sum.inrₗ k, ?_⟩
    simp only [orderedSelectedCoordinates, ofLex_toLex, hk, Option.elim_some]
  · exact orderedSelectedCoordinates_compatibility seed hzero hseed data A q hq hpref hnew

end CircleDomainRigidity

end

end OAI
