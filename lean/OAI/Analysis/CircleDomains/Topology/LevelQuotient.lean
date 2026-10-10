import OAI.Analysis.CircleDomains.Topology.GenericLevelTopology

namespace OAI

/-!
# Restricting the quotient to a compact level union

The original quotient acts on the whole compact physical space. For a
compact level union `H`, restrict it to `π ⁻¹' H → H`. Connected fibers
remain connected, omitted points still map into compact totally
disconnected dust, and the induced-metric Hausdorff length is exactly
the physical length of `(π ⁻¹' H) ∩ G`.
-/

open Set Metric MeasureTheory Function
open scoped ENNReal

namespace CircleDomainRigidity

def levelQuotientMap {X Y : Type*} (π : Y → X) (H : Set X) : (π ⁻¹' H) → H :=
  fun y => ⟨π y.val, y.property⟩

theorem continuous_levelQuotientMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {π : Y → X} (hπ : Continuous π) (H : Set X) :
    Continuous (levelQuotientMap π H) :=
  (hπ.comp continuous_subtype_val).subtype_mk _

theorem surjective_levelQuotientMap {X Y : Type*} {π : Y → X}
    (hsurj : Surjective π) (H : Set X) : Surjective (levelQuotientMap π H) := by
  intro x
  obtain ⟨y, hy⟩ := hsurj x.val
  have hyH : y ∈ π ⁻¹' H := by simpa only [mem_preimage, hy] using x.property
  exact ⟨⟨y, hyH⟩, Subtype.ext hy⟩

theorem connected_fibers_levelQuotientMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {π : Y → X} (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x})) (H : Set X) (x : H) :
    IsConnected (levelQuotientMap π H ⁻¹' {x}) := by
  have himage : (Subtype.val : (π ⁻¹' H) → Y) '' (levelQuotientMap π H ⁻¹' {x}) =
      π ⁻¹' {x.val} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact congrArg Subtype.val hz
    · intro hy
      have hyH : y ∈ π ⁻¹' H := by
        change π y ∈ H
        simpa only [show π y = x.val from hy] using x.property
      exact ⟨⟨y, hyH⟩, Subtype.ext hy, rfl⟩
  refine ⟨?_, Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
  · obtain ⟨y, hy⟩ := surjective_levelQuotientMap hsurj H x
    exact ⟨y, hy⟩
  · rw [himage]
    exact (hfiber x.val).isPreconnected

/-- The finite-continuum bound on an actual compact quotient level set,
from its physical level length. -/
theorem finite_large_continuum_bound_on_level
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G : Set Y} (hG : IsOpen G) {B H : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B) (hdust : π '' Gᶜ ⊆ B)
    (hH : IsCompact H)
    (hlength : (μH[1] : Measure Y) ((π ⁻¹' H) ∩ G) < ∞) :
    HasFiniteLargeContinuumBound H := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have hpreclosed : IsClosed (π ⁻¹' H) := hH.isClosed.preimage hπ
  let : CompactSpace (π ⁻¹' H) := isCompact_iff_compactSpace.mp hpreclosed.isCompact
  let GH : Set (π ⁻¹' H) := Subtype.val ⁻¹' G
  let BH : Set H := Subtype.val ⁻¹' B
  have hGH : IsOpen GH := hG.preimage continuous_subtype_val
  have hBH : IsCompact BH := (hB.isClosed.preimage continuous_subtype_val).isCompact
  have hTDH : IsTotallyDisconnected BH := by
    apply isTotallyDisconnected_of_image continuous_subtype_val.continuousOn
      Subtype.val_injective
    intro C hC hconn
    apply hTD C ?_ hconn
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hC hz
    exact hx
  have hdustH : levelQuotientMap π H '' GHᶜ ⊆ BH := by
    rintro _ ⟨y, hy, rfl⟩
    exact hdust ⟨y.val, hy, rfl⟩
  have hiso : Isometry (Subtype.val : (π ⁻¹' H) → Y) := fun _ _ => rfl
  have hlengthH : (μH[1] : Measure (π ⁻¹' H)) GH < ∞ := by
    rw [← hiso.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 1))]
    simpa only [GH, Subtype.image_preimage_coe] using hlength
  exact finite_large_continuum_bound_of_compact_quotient_dust
    (levelQuotientMap π H) (continuous_levelQuotientMap hπ H)
    (surjective_levelQuotientMap hsurj H) (connected_fibers_levelQuotientMap hsurj hfiber H)
    hGH hBH hTDH hdustH hlengthH

/-- Countability and local connectedness for the actual compact level
union, without replacing the whole physical space by an unspecified
finite-length ambient space. -/
theorem level_topology_of_finite_physical_length
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G : Set Y} (hG : IsOpen G) {B H : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B) (hdust : π '' Gᶜ ⊆ B)
    (hH : IsCompact H)
    (hlength : (μH[1] : Measure Y) ((π ⁻¹' H) ∩ G) < ∞) :
    HasFiniteLargeContinuumBound H ∧
      {C : Set H | (∃ x, C = connectedComponent x) ∧ C.Nontrivial}.Countable ∧
      ∀ C : Set H, IsCompact C → IsConnected C → LocallyConnectedSpace C := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have hbound := finite_large_continuum_bound_on_level π hπ hsurj hfiber
    hG hB hTD hdust hH hlength
  exact ⟨hbound, countable_nontrivial_connectedComponents hbound,
    fun _ hcompact hconn =>
      locallyConnected_subcontinuum_of_finite_large_continuum_bound hbound hcompact hconn⟩

end CircleDomainRigidity

end OAI
