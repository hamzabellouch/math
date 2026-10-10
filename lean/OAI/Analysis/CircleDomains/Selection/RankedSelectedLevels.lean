import OAI.Analysis.CircleDomains.Rigidity.SeededMaskedSelection
import OAI.Analysis.CircleDomains.Selection.RankedTupleCompatibility
import Mathlib.Logic.Equiv.Nat

namespace OAI

/-! Enumerating the selected labels does not change their inherited order.
This supplies exactly the ranked compatibility used by the tag-law proofs. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 def selectedCoordinateEnumeration : ℕ ≃ ℕ ⊕ₗ ℕ :=
  Equiv.natSumNatEquivNat.symm.trans toLex

 omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem ranked_compatibility_of_ordered_family
    {L : Type*} [LinearOrder L] (rank : ℕ → L)
    (D : L → Set (Sphere × UnitAddCircle)) (F : Set Sphere)
    (H : ℕ → Set (UnitAddCircle × Sphere))
    (hH : ∀ i, H i = Prod.swap ⁻¹' D (rank i))
    (hcompat : ∀ (j : L) (n : ℕ) (labels : Fin n → L), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure F (D j) D labels) = 0) :
    RankedLevelNullCompatibility rank H F := by
  have hrel : levelRelation H = fun i => D (rank i) := by
    funext i
    ext p
    rw [levelRelation, hH i]
    rfl
  intro j n labels hlt
  rw [hrel]
  have h := hcompat (rank j) n (rank ∘ labels) hlt
  rw [UngatedRealTest.freeComponentFailure_congr_selected F (D (rank j)) D
    (fun i => D (rank i)) (rank ∘ labels) labels (fun _ => rfl)] at h
  simpa only [MeasureTheory.volume_pi] using h

 theorem selected_pathData_ranked_compatibility
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {L : Type*} [LinearOrder L] (rank : ℕ → L)
    (D : L → SelectableMaskedCoordinate d π)
    (hcompat : ∀ (j : L) (n : ℕ) (labels : Fin n → L), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
          (fun k => (D k).coordinate.graph) labels) = 0) :
    RankedLevelNullCompatibility rank
      (SelectableMaskedCoordinate.pathData (D ∘ rank)).levels (d.dust \ ⋃ k, (D k).flags) :=
  ranked_compatibility_of_ordered_family rank (fun k => (D k).coordinate.graph) _ _
    (fun _ => rfl) hcompat

end CircleDomainRigidity

end

end OAI
