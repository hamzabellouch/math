import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveGeometricGeneration
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.AlignedGroups

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AlignedPolygonGeneration

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

noncomputable def polygonAlignedGroup (I : Finset (Fin (m+1))) :
    Subgroup (polygonFullGroup a (m+1)) :=
  alignedGroup (sourceLatticeFullMap a r m hm)
    (fun b : SmallConditional m => conditionalHom (initialTest a r b.1) b.2.val)
    (fun b => b.2.val.support ⊆ I)

theorem fiveTrack_support_subset (ι : Fin 5 ↪ Fin (m+1))
    (g : alternatingGroup (Fin 5)) :
    (fiveTrackHom ι g).support ⊆ Finset.univ.map ι := by
  classical
  intro i hi
  by_contra hn
  have hn' : i ∉ Set.range ι := by simpa using hn
  exact (Equiv.Perm.mem_support.mp hi)
    (Equiv.Perm.viaEmbedding_apply_of_notMem g.val ι i hn')

theorem fiveTrack_initial_aligned (ι : Fin 5 ↪ Fin (m+1)) (j : Fin 5) :
    ConditionalAvailable (fiveTrackHom ι)
      (polygonAlignedGroup a r m hm (Finset.univ.map ι)) (initialTest a r j) := by
  intro g
  exact alignedGroup_input _ _ _
    ((j,⟨fiveTrackHom ι g,fiveTrack_sign ι g,fiveTrack_support ι g⟩) : SmallConditional m)
    (fiveTrack_support_subset m ι g)

theorem fiveTrack_translate_aligned (ι : Fin 5 ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ Set.range ι) (U : polygonAlgebra a)
    (hU : ConditionalAvailable (fiveTrackHom ι)
      (polygonAlignedGroup a r m hm (Finset.univ.map ι)) U)
    (u : CutRing × CutRing) :
    ConditionalAvailable (fiveTrackHom ι)
      (polygonAlignedGroup a r m hm (Finset.univ.map ι))
      ⟨translate a u ⁻¹' U.val,polygon_preimage_translate u U.property⟩ := by
  classical
  obtain ⟨k,d,hk,hd⟩ := sourceLatticeFullMap_prescribed a r m hm
    (Finset.univ.map ι) b (by simpa using hb) (fun _ => -u)
  intro g
  have hd' : ∀ i, fiveTrackHom ι g i ≠ i → d i = -u := by
    intro i hi
    exact hd i (fiveTrack_support_subset m ι g (Equiv.Perm.mem_support.mpr hi))
  have he := conditional_translation_conjugate U (fiveTrackHom ι g) d (-u) hd'
  simp only [neg_neg] at he
  rw [he,← hk]
  exact alignedGroup_conjugate _ _ _ k (hU g)

noncomputable def fiveTrackAlignedBoolean (ι : Fin 5 ↪ Fin (m+1)) :
    BooleanSubalgebra (Set (GenericSquare a)) :=
  conditionalBoolean (fiveTrackHom ι) (polygonAlignedGroup a r m hm (Finset.univ.map ι))
    (fiveTrack_initial_aligned a r m hm ι 0)

theorem fiveTrackAlignedBoolean_initial (ι : Fin 5 ↪ Fin (m+1)) (j : Fin 5) :
    (initialTest a r j).val ∈ fiveTrackAlignedBoolean a r m hm ι :=
  ⟨(initialTest a r j).property,fiveTrack_initial_aligned a r m hm ι j⟩

theorem fiveTrackAlignedBoolean_translate (ι : Fin 5 ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ Set.range ι) (u : CutRing × CutRing)
    {U : Set (GenericSquare a)} (hU : U ∈ fiveTrackAlignedBoolean a r m hm ι) :
    translate a u ⁻¹' U ∈ fiveTrackAlignedBoolean a r m hm ι := by
  obtain ⟨hU,hU'⟩ := hU
  exact ⟨polygon_preimage_translate u hU,
    fiveTrack_translate_aligned a r m hm ι b hb ⟨U,hU⟩ hU' u⟩

theorem fiveTrackAlignedBoolean_coordinate (ι : Fin 5 ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ Set.range ι) (j : Fin 2) (z : CutRing) :
    halfPlane a (Fin.castLE (by omega) j) z ∈ fiveTrackAlignedBoolean a r m hm ι := by
  apply coordinate_cuts_generated _ j
    (fun u _ hU => fiveTrackAlignedBoolean_translate a r m hm ι b hb u hU)
  fin_cases j
  · exact fiveTrackAlignedBoolean_initial a r m hm ι 1
  · exact fiveTrackAlignedBoolean_initial a r m hm ι 2

theorem fiveTrack_polygon_aligned (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1)) (hb : b ∉ Set.range ι)
    (U : polygonAlgebra a) : ConditionalAvailable (fiveTrackHom ι)
      (polygonAlignedGroup a r m hm (Finset.univ.map ι)) U := by
  let B := fiveTrackAlignedBoolean a r m hm ι
  have hcoord := fiveTrackAlignedBoolean_coordinate a r m hm ι b hb
  have htrans := fun u U hU => fiveTrackAlignedBoolean_translate a r m hm ι b hb u (U := U) hU
  have hv : U.val ∈ B := by
    apply polygon_induction (P := fun U => U ∈ B) ?_ BooleanSubalgebra.bot_mem
      (fun _ _ hU hV => BooleanSubalgebra.sup_mem hU hV)
      (fun _ hU => BooleanSubalgebra.compl_mem hU) U.property
    intro j z
    fin_cases j
    · exact hcoord 0 z
    · exact hcoord 1 z
    · exact slope_cuts_generated r hr B htrans hcoord 2 (Or.inl rfl)
        (fiveTrackAlignedBoolean_initial a r m hm ι 3) z
    · exact slope_cuts_generated r hr B htrans hcoord 3 (Or.inr rfl)
        (fiveTrackAlignedBoolean_initial a r m hm ι 4) z
  exact hv.choose_spec

end AlignedPolygonGeneration

end SimpleAmenable
end
end

end OAI
