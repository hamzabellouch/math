import OAI.Geometry.SurfaceImmersion.Primitive.CircularDiskTopology
import OAI.Geometry.SurfaceImmersion.Atlas.SurfacePhaseCharts

namespace OAI

/-! Compact primitive disks and their boundaries in the actual phase chart. -/
noncomputable section
open Set Filter Manifold
open scoped Topology
namespace ClosedSurfaceR4
open SmallModes
variable {M : Type*} [TopologicalSpace M]

lemma compact_phase_disk_geometry (E : OpenPartialHomeomorph M Base)
    {D : Set M} (hD : IsOpen D) (hK : IsCompact (closure D))
    (hS : closure D ⊆ E.source) :
    IsOpen (E '' D) ∧ closure (E '' D) = E '' closure D ∧
      frontier (E '' D) = E '' frontier D ∧ IsCompact (closure (E '' D)) := by
  have hSD : D ⊆ E.source := subset_trans subset_closure hS
  have hI : E.IsImage D (E '' D) := by
    intro p hp
    constructor
    · rintro ⟨q,hq,he⟩
      have hqp := E.injOn (hSD hq) hp he
      exact hqp ▸ hq
    · exact fun hpD => ⟨p,hpD,rfl⟩
  have hIE : E.target ∩ E '' D = E '' D := inter_eq_right.mpr (by
    rintro _ ⟨p,hp,rfl⟩
    exact E.map_source (hSD hp))
  have hO : IsOpen (E '' D) := by
    rw [← hIE]
    exact hI.isOpen_iff.mp (E.open_source.inter hD)
  have hC : IsCompact (E '' closure D) := hK.image_of_continuousOn (E.continuousOn.mono hS)
  have hc : closure (E '' D) = E '' closure D := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono subset_closure) hC.isClosed
    · rintro _ ⟨p,hp,rfl⟩
      exact (hI.closure (hS hp)).mpr hp
  have hf : frontier (E '' D) = E '' frontier D := by
    rw [frontier,hO.interior_eq,hc,frontier,hD.interior_eq]
    ext y
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,hn⟩
      exact ⟨p,⟨hp,fun hpD => hn ⟨p,hpD,rfl⟩⟩,rfl⟩
    · rintro ⟨p,⟨hp,hn⟩,rfl⟩
      refine ⟨⟨p,hp,rfl⟩,?_⟩
      rintro ⟨q,hq,he⟩
      have hqp := E.injOn (hSD hq) (hS hp) he
      exact hn (hqp ▸ hq)
  exact ⟨hO,hc,hf,hc ▸ hC⟩

lemma compact_phase_boundary_neighborhood {D Ω G : Set Base}
    (hD : IsOpen D) (hK : IsCompact (closure D))
    (hΩ : IsOpen Ω) (hDΩ : closure D ⊆ Ω)
    (hG : IsOpen G) (hDG : frontier D ⊆ G) :
    ∃ V : Set Base, IsOpen V ∧ IsCompact (closure V) ∧ closure D ⊆ V ∧
      closure V ⊆ Ω ∧ closure V \ D ⊆ G := by
  have hcover : closure D ⊆ Ω ∩ (D ∪ G) := by
    intro p hp
    refine ⟨hDΩ hp,?_⟩
    by_cases hi : p ∈ D
    · exact Or.inl hi
    · exact Or.inr (hDG ⟨hp,by simpa only [hD.interior_eq] using hi⟩)
  obtain ⟨V,hV,hKV,hVG⟩ := hK.exists_isOpen_closure_subset
    ((hΩ.inter (hD.union hG)).mem_nhdsSet.mpr hcover)
  obtain ⟨B,hB,hKB,hBc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  let W := V ∩ B
  have hWV : closure W ⊆ closure V := closure_mono inter_subset_left
  have hWB : closure W ⊆ closure B := closure_mono inter_subset_right
  refine ⟨W,hV.inter hB,hBc.of_isClosed_subset isClosed_closure hWB,
    fun p hp => ⟨hKV hp,hKB hp⟩,fun p hp => (hVG (hWV hp)).1,?_⟩
  intro p hp
  exact (hVG (hWV hp.1)).2.resolve_left hp.2

end ClosedSurfaceR4

end

end OAI
