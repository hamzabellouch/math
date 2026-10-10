import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.AlignedPolygonGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AlignedFiniteTables

variable {α G : Type*} [Group G] (f : α → G)

theorem finite_table_lift_in_subgroup_eventually (L : ℕ)
    (K : Subgroup (BoundedRelationCover L f)) {T : Type*} [Group T] [Finite T]
    (φ : T →* G) (hφ : ∀ s, φ s ∈ K.map (coverMap L f)) :
    ∃ B : ℕ, ∃ hLB : L ≤ B, ∀ M : ℕ, ∀ hBM : B ≤ M,
      ∃ ρ : T →* BoundedRelationCover M f,
        (coverMap M f).comp ρ = φ ∧
        ρ.range ≤ K.map (coverTransition f (le_trans hLB hBM)) := by
  choose y hy hyq using hφ
  choose w hw using fun s => PresentedGroup.mk_surjective (shortRelations L f) (y s)
  have hwp : ∀ s, FreeGroup.lift f (w s) = φ s := by
    intro s
    rw [← coverMap_mk L f,hw s,hyq s]
  obtain ⟨B,hB⟩ := finite_table_lift_eventually f φ w hwp
  refine ⟨max L B,le_max_left _ _,fun M hM => ?_⟩
  obtain ⟨ρ,hρ,hρw⟩ := hB M (le_trans (le_max_right _ _) hM)
  refine ⟨ρ,hρ,?_⟩
  rintro z ⟨s,rfl⟩
  refine ⟨y s,hy s,?_⟩
  rw [← hw s,coverTransition_mk,hρw s]

end AlignedFiniteTables

section SourceAlignedTableCompatibility

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

theorem sourceAlignedGroup_map_full (M : ℕ)
    (t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (ht : (coverMap M (alternatingGenerator a r m hm)).comp t = sourceLatticeMap a r m hm)
    (I : Finset (Fin (m+1))) :
    (sourceAlignedGroup a r m hm M t I).map
      ((polygonAlternatingGroup a (m+1)).subtype.comp
        (coverMap M (alternatingGenerator a r m hm))) = polygonAlignedGroup a r m hm I := by
  rw [sourceAlignedGroup,alignedGroup_map]
  have htrans : ((polygonAlternatingGroup a (m+1)).subtype.comp
        (coverMap M (alternatingGenerator a r m hm))).comp t =
      sourceLatticeFullMap a r m hm := by
    rw [MonoidHom.comp_assoc,ht]
    rfl
  rw [htrans]
  rfl

theorem sourceAlignedGroup_transition {L M : ℕ} (hLM : L ≤ M)
    (t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      BoundedRelationCover L (alternatingGenerator a r m hm)) (I : Finset (Fin (m+1))) :
    (sourceAlignedGroup a r m hm L t I).map
        (coverTransition (alternatingGenerator a r m hm) hLM) =
      sourceAlignedGroup a r m hm M
        ((coverTransition (alternatingGenerator a r m hm) hLM).comp t) I := by
  rw [sourceAlignedGroup,alignedGroup_map]
  rfl

theorem fiveTrack_conditional_preimage_aligned
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (M : ℕ)
    (t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (ht : (coverMap M (alternatingGenerator a r m hm)).comp t = sourceLatticeMap a r m hm)
    (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1)) (hb : b ∉ Set.range ι)
    (U : polygonAlgebra a) (g : alternatingGroup (Fin 5)) :
    ∃ y ∈ sourceAlignedGroup a r m hm M t (Finset.univ.map ι),
      ((coverMap M (alternatingGenerator a r m hm) y).val : polygonFullGroup a (m+1)) =
        conditionalHom U (fiveTrackHom ι g) := by
  have hh := fiveTrack_polygon_aligned a r m hm hr ι b hb U g
  rw [← sourceAlignedGroup_map_full a r m hm M t ht] at hh
  exact hh

end SourceAlignedTableCompatibility

end SimpleAmenable
end
end

end OAI
