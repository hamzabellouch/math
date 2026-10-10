import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Selection.ExactRealSelections
import OAI.Analysis.CircleDomains.Selection.PresentedRealCoordinates
import OAI.Analysis.CircleDomains.Selection.RestrictedSelectedFamily
import OAI.Analysis.CircleDomains.Uniformization.MixedAssignedLimit

namespace OAI

/-! The countable selected family produces actual mixed finite models. Every chosen real
presentation, including a real barrier selected after the seed, is retained with its exact
physical and quotient functions. The finite coordinates keep the selected family's order. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

structure SelectedMixedModels
    (hsch : PlanarSchoenflies) (base : PathCodeData Sphere Sphere)
    (hU : IsOpen base.quotientDomain) (hdense : Dense base.quotientDomain)
    (π : Sphere → Sphere)
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hB : base.dust = π '' base.physicalDomainᶜ)
    {L : Type*} [LinearOrder L]
    (D : L → SelectableMaskedCoordinate base π)
    (presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate)
    (B₀ : Set base.dust) where
  marks : Set base.dust
  marks_countable : marks.Countable
  mandatory : B₀ ⊆ marks
  flags : ∀ l x, x ∈ (D l).flags → x ∈ Subtype.val '' marks
  singular : ∀ l, (D l).coordinate.singular ∈ marks
  support : ∀ l s, (D l).coordinate.upper s - (D l).coordinate.lower s ≠ 0 → s ∈ marks
  realLabels : ℕ → L
  real_injective : Injective realLabels
  realPresentation : ∀ n, RealCoordinatePresentation base π (D (realLabels n)).coordinate
  real_selected : ∀ n, presentation (realLabels n) = Sum.inl (realPresentation n)
  real_cover : ∀ l (r : RealCoordinatePresentation base π (D l).coordinate),
    presentation l = Sum.inl r → ∃ n, realLabels n = l ∧
      (realPresentation n).coordinate.physical = r.coordinate.physical ∧
      (realPresentation n).coordinate.quotient = r.coordinate.quotient
  model : MixedModelExhaustion
    (realCoordinatesFromPresentations base hU hdense π he hB
      (fun l => (D l).coordinate) realLabels realPresentation marks support)
    (fun l => (D l).coordinate.restrictMarks marks (singular l) (support l)) realLabels
    (markedNeighborhoods (fun s : marks => s.val.val)) modelError modelError

 theorem exists_selected_mixed_models
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    (base : PathCodeData Sphere Sphere) (hU : IsOpen base.quotientDomain)
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hinfty : OnePoint.infty ∈ base.physicalDomain) (hdense : Dense base.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hB : base.dust = π '' base.physicalDomainᶜ)
    (hTD : IsTotallyDisconnected base.dust) (hUB : Disjoint base.quotientDomain base.dust)
    {L : Type*} [LinearOrder L] [Countable L]
    (D : L → SelectableMaskedCoordinate base π)
    (presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate)
    (hinfinite : {l | ∃ r, presentation l = Sum.inl r}.Infinite)
    (hcompat : ∀ (j : L) (n : ℕ) (labels : Fin n → L), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (base.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
          (fun k => (D k).coordinate.graph) labels) = 0)
    (B₀ : Set base.dust) (hB₀ : B₀.Countable) :
    Nonempty (SelectedMixedModels hsch base hU hdense π he hB D presentation B₀) := by
  let marks : Set base.dust := Subtype.val ⁻¹' (⋃ k, (D k).flags) ∪ B₀
  have hmarks : marks.Countable :=
    ((countable_iUnion fun k => (D k).flags_countable).preimage Subtype.val_injective).union hB₀
  let : Countable marks := hmarks.to_subtype
  have hflags (l : L) (x : Sphere) (hx : x ∈ (D l).flags) : x ∈ Subtype.val '' marks :=
    ⟨⟨x, (D l).flags_dust hx⟩, Or.inl (mem_iUnion.mpr ⟨l, hx⟩), rfl⟩
  have hsing (l : L) : (D l).coordinate.singular ∈ marks :=
    Or.inl (mem_iUnion.mpr ⟨l, (D l).singular_marked⟩)
  have hsupp (l : L) (s : base.dust)
      (hs : (D l).coordinate.upper s - (D l).coordinate.lower s ≠ 0) : s ∈ marks := by
    apply Or.inl
    apply mem_iUnion.mpr
    refine ⟨l, (D l).weight_support ?_⟩
    change (D l).coordinate.dustWeight s.val ≠ 0
    rw [MaskedCoordinateData.dustWeight, dite_eq_left s.property]
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (lt_of_le_of_ne ((D l).coordinate.width_nonneg s) (Ne.symm hs))
  obtain ⟨ι, hι, R, hR, hcover⟩ := exists_injective_real_presentations
    (fun l => (D l).coordinate) presentation hinfinite
  have hcomp (j : L) (n : ℕ) (labels : Fin n → L) (hlt : ∀ i, labels i < j) :
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' base.physicalDomainᶜ) \ range (fun s : marks => s.val.val))
          (D j).coordinate.graph (fun k => (D k).coordinate.graph) labels) = 0 := by
    apply measure_mono_null (freeComponentFailure_mono_free ?_ _ _ labels) (hcompat j n labels hlt)
    intro x hx
    refine ⟨hB.symm ▸ hx.1, ?_⟩
    intro hxflags
    obtain ⟨l, hl⟩ := mem_iUnion.mp hxflags
    obtain ⟨s, hs, hval⟩ := hflags l x hl
    exact hx.2 ⟨⟨s, hs⟩, hval⟩
  obtain ⟨M⟩ := exists_mixed_exhaustion_from_presentations hsard hsch hcompact hfinite
    base hU hG hconn hinfty hdense π hπ hclosed hsurj hr he hB hTD hUB
    (fun l => (D l).coordinate) ι hι R marks hsing hsupp hcomp
    (markedNeighborhoods (fun s : marks => s.val.val)) (markedNeighborhoods_nhds _)
    modelError modelError modelError_pos modelError_pos
  exact ⟨⟨marks, hmarks, subset_union_right, hflags, hsing, hsupp, ι, hι, R, hR, hcover, M⟩⟩

end CircleDomainRigidity

end

end OAI
