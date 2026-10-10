import OAI.Analysis.CircleDomains.Rigidity.SelectableMaskedCoordinate
import OAI.Analysis.CircleDomains.Rigidity.OrderedMaskedSelection

namespace OAI

/-! Reduce the selected family to one countable set of marks while
retaining its ordered compatibility and its real seed. No physical
coordinate, mask, or boundary graph changes in this reduction. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_restricted_selected_family
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (hB : d.dust = π '' d.physicalDomainᶜ)
    {L : Type*} [LinearOrder L] [Countable L]
    (D : L → SelectableMaskedCoordinate d π)
    (hcompat : ∀ (j : L) (n : ℕ) (labels : Fin n → L), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
          (fun k => (D k).coordinate.graph) labels) = 0)
    (B₀ : Set d.dust) (hB₀ : B₀.Countable) :
    ∃ A : Set d.dust, A.Countable ∧ B₀ ⊆ A ∧
      (∀ i, (D i).coordinate.singular ∈ A) ∧
      ∃ C : L → MaskedCoordinateData d.physicalDomain d.quotientDomain π
          (fun s : A => s.val.val),
        (∀ i, (C i).graph = (D i).coordinate.graph ∧
          (C i).mask = (D i).coordinate.mask ∧
          (C i).physical = (D i).coordinate.physical) ∧
        (∀ (i : L) (R : ℝ), 0 ≤ R →
          (C i).sourceStokesBudget R ≤ (D i).coordinate.sourceStokesBudget R) ∧
        (∀ (j : L) (n : ℕ) (labels : Fin n → L), (∀ i, labels i < j) →
          (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
            (freeComponentFailure ((π '' d.physicalDomainᶜ) \ range (fun s : A => s.val.val))
              (C j).graph (fun k => (C k).graph) labels) = 0) ∧
        ∀ (ι : ℕ → L), RealCoordinateSubfamily (fun i => (D i).coordinate) ι →
          Nonempty (RealCoordinateSubfamily C ι) := by
  let flags : Set Sphere := ⋃ k, (D k).flags
  have hflags : flags.Countable := countable_iUnion (fun k => (D k).flags_countable)
  let A : Set d.dust := Subtype.val ⁻¹' flags ∪ B₀
  have hA : A.Countable := (hflags.preimage Subtype.val_injective).union hB₀
  have hsing (i : L) : (D i).coordinate.singular ∈ A :=
    Or.inl (mem_iUnion.mpr ⟨i, (D i).singular_marked⟩)
  have hsupp (i : L) (s : d.dust)
      (hs : (D i).coordinate.upper s - (D i).coordinate.lower s ≠ 0) : s ∈ A := by
    apply Or.inl
    apply mem_iUnion.mpr
    refine ⟨i, (D i).weight_support ?_⟩
    change (D i).coordinate.dustWeight s.val ≠ 0
    rw [MaskedCoordinateData.dustWeight, dite_eq_left s.property]
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (lt_of_le_of_ne ((D i).coordinate.width_nonneg s) (Ne.symm hs))
  let C (i : L) := (D i).coordinate.restrictMarks A (hsing i) (hsupp i)
  refine ⟨A, hA, subset_union_right, hsing, C, (fun _ => ⟨rfl, rfl, rfl⟩), ?_, ?_, ?_⟩
  · intro i R hR
    exact (D i).coordinate.restrictMarks_sourceStokesBudget_le A (hsing i) (hsupp i) hR
  · intro j n labels hlt
    apply measure_mono_null (freeComponentFailure_mono_free ?_ _ _ labels) (hcompat j n labels hlt)
    intro x hx
    have hxB : x ∈ d.dust := hB.symm ▸ hx.1
    refine ⟨hxB, ?_⟩
    intro hxflag
    exact hx.2 ⟨⟨⟨x, hxB⟩, Or.inl hxflag⟩, rfl⟩
  · intro ι R
    exact ⟨R.restrictMarks A hsing hsupp⟩

end CircleDomainRigidity

end

end OAI
