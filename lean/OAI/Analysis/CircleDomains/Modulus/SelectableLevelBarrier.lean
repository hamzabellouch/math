import OAI.Analysis.CircleDomains.Selection.SelectableRealFamily
import OAI.Analysis.CircleDomains.Selection.RealSeedPresentation
import OAI.Analysis.CircleDomains.Modulus.CompatibleLevelBarrier

namespace OAI

/-! The small real-barrier alternative supplies an actual selectable
coordinate compatible with every previously selected real or period
coordinate. Its flags and presentation are constructed from the barrier. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_selectable_level_barrier
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdense : Dense d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ) (p : d.dust)
    (previous : PriorLevelFamily d.physicalDomain π)
    (flags EStar : Set Sphere) (hinfty : π OnePoint.infty ∈ interior EStar)
    (regions : ℕ → Set Sphere) (f : d.quotientDomain → Sphere) (W : Set Sphere)
    (R : CompatibleLevelBarrier d π previous flags EStar regions f W)
    (A : Set (SelectableMaskedCoordinate d π))
    (label : SelectableMaskedCoordinate d π → ℕ)
    (hflags : ∀ a ∈ A, a.flags ⊆ flags)
    (hgraphs : ∀ a ∈ A, a.coordinate.graph = previous.graph (label a)) :
    ∃ c : SelectableMaskedCoordinate d π, c.CompatibleWith A ∧
      c.coordinate.graph = circleBandGraph d.quotientDomain R.coordinate.quotient ∧
      ∃ P : RealCoordinatePresentation d π c.coordinate, P.coordinate = R.coordinate := by
  have hempty (j n : ℕ) (labels : Fin n → ℕ) (_ : ∀ i, labels i < j) :
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ d.dust)
          (circleBandGraph d.quotientDomain R.coordinate.quotient)
          (fun _ => circleBandGraph d.quotientDomain R.coordinate.quotient) labels) = 0 := by
    simp [freeComponentFailure]
  let F := realCoordinateFamily d hU hdense π he hB (fun _ => R.coordinate)
    d.dust (Subset.refl _) (fun _ => R.weight) (fun _ => R.weight_finite)
    (fun _ _ hx _ => hx) (fun _ => R.band_bound) hempty
  let C := F.maskedCoordinate hG p 0
  obtain ⟨c, hc, hmark⟩ := SelectableMaskedCoordinate.exists_of_real hcoarea d hU hG π he
    R.coordinate C rfl (R.exclusions ∩ d.dust)
    (R.exclusions_countable.mono inter_subset_left) inter_subset_right
  have hgraph : c.coordinate.graph = circleBandGraph d.quotientDomain R.coordinate.quotient := by
    rw [hc]
    rfl
  refine ⟨c, ⟨?_, ?_⟩, hgraph, ?_⟩
  · intro a ha x hx
    exact hmark ⟨R.prior_flags (hflags a ha hx), a.flags_dust hx⟩
  · intro n q hq
    rw [hgraph]
    have hz := R.finite_compatibility n (label ∘ q)
    rw [UngatedRealTest.freeComponentFailure_congr_selected (d.dust \ R.exclusions)
      (circleBandGraph d.quotientDomain R.coordinate.quotient) previous.graph
      (fun i : Fin n => (q i).coordinate.graph) (label ∘ q) id
      (fun i => (hgraphs (q i) (hq i)).symm)] at hz
    apply measure_mono_null (freeComponentFailure_mono_free ?_ _ _ id) hz
    intro x hx
    exact ⟨hx.1, fun hr => hx.2 (hmark ⟨hr, hx.1⟩)⟩
  · refine ⟨{
      coordinate := R.coordinate
      graph_eq := hgraph
      mask_eq_univ := by rw [hc]; rfl
      physical_eq := by intro x; rw [hc]; rfl
      band_width := by intro s; rw [hc]; rfl
      compactSupport := ((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹' interior EStar)ᶜ
      isCompact_support := isCompact_finite_preimage
        (isOpen_interior.preimage hπ).isClosed_compl (fun h => h hinfty)
      zero_off := ?_
      zero_infty := fun _ => R.zero _ (interior_subset hinfty) }, rfl⟩
    intro z _ hz
    apply R.zero
    apply interior_subset
    by_contra hn
    exact hz hn

end CircleDomainRigidity

end

end OAI
