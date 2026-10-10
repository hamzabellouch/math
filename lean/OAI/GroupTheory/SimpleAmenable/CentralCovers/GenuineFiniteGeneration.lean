import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ShiftedSlots
import OAI.GroupTheory.SimpleAmenable.CentralCovers.BoundedRelationCover
import OAI.GroupTheory.SimpleAmenable.Configurations.FiveTrackGeneration
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveGeometricGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section GenuineFiniteGeneration

theorem fiveTrackBoolean_polygon (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1)) (hb : b ∉ Set.range ι)
    (U : polygonAlgebra a) : U.val ∈ fiveTrackBoolean a r m ι := by
  let B := fiveTrackBoolean a r m ι
  have hcoord := fiveTrackBoolean_coordinate a r m ι b hb
  have htrans := fun u U hU => fiveTrackBoolean_translate a r m ι b hb u (U := U) hU
  apply polygon_induction (P := fun U => U ∈ B) ?_ BooleanSubalgebra.bot_mem
    (fun _ _ hU hV => BooleanSubalgebra.sup_mem hU hV)
    (fun _ hU => BooleanSubalgebra.compl_mem hU) U.property
  intro j z
  fin_cases j
  · exact hcoord 0 z
  · exact hcoord 1 z
  · exact slope_cuts_generated r hr B htrans hcoord 2 (Or.inl rfl)
      (fiveTrackBoolean_initial a r m ι 3) z
  · exact slope_cuts_generated r hr B htrans hcoord 3 (Or.inr rfl)
      (fiveTrackBoolean_initial a r m ι 4) z

theorem fiveTrack_polygon_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1)) (hb : b ∉ Set.range ι)
    (U : polygonAlgebra a) : ConditionalAvailable (fiveTrackHom ι) (sourceGenerated a r m) U := by
  obtain ⟨_,h⟩ := fiveTrackBoolean_polygon a r m hr ι b hb U
  exact h

private theorem extend_three_tracks {m : ℕ} (hm : 15 ≤ m) (s : Fin 3 ↪ Fin m) :
    ∃ (ι : Fin 5 ↪ Fin m) (b : Fin m), (∀ i, ι (threeInFive i) = s i) ∧ b ∉ Set.range ι := by
  obtain ⟨e,he⟩ := fresh_nine_tracks hm s s
  let t : Fin 5 → Fin m := ![s 0,s 1,s 2,e 0,e 1]
  have hs : Function.Injective t := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals dsimp only [t,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_four] at hij
    all_goals first | rfl | exact False.elim (by have := s.injective hij; contradiction) |
      exact False.elim (by have := e.injective hij; contradiction) |
      exact False.elim ((he _ _).1 hij) | exact False.elim ((he _ _).1 hij.symm)
  refine ⟨⟨t,hs⟩,e 2,?_,?_⟩
  · intro i
    fin_cases i <;> rfl
  · rintro ⟨i,hi⟩
    fin_cases i
    all_goals dsimp only [Function.Embedding.coeFn_mk,t,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four] at hi
    all_goals first | exact (he _ _).1 hi.symm |
      exact False.elim (by have := e.injective hi; contradiction)

theorem trackCycle_viaEmbedding {m n : ℕ} (ι : Fin m ↪ Fin n) (s : Fin 3 ↪ Fin m) :
    (trackCycle s).viaEmbedding ι = trackCycle (s.trans ι) := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨y,rfl⟩ := hx
    rw [Equiv.Perm.viaEmbedding_apply]
    by_cases hy : y ∈ Set.range s
    · obtain ⟨i,rfl⟩ := hy
      rw [trackCycle_apply]
      exact (trackCycle_apply (s.trans ι) i).symm
    · rw [trackCycle_apply_of_notMem s hy,trackCycle_apply_of_notMem (s.trans ι)]
      rintro ⟨i,hi⟩
      exact hy ⟨i,ι.injective hi⟩
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx,trackCycle_apply_of_notMem]
    rintro ⟨i,hi⟩
    exact hx ⟨s i,hi⟩

theorem conditional_cycle_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1)
    (U : polygonAlgebra a) (s : Fin 3 ↪ Fin (m+1)) :
    conditionalHom U (trackCycle s) ∈ sourceGenerated a r m := by
  obtain ⟨ι,b,he,hb⟩ := extend_three_tracks hm s
  have hg : trackCycle threeInFive ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have h := fiveTrack_polygon_generated a r m hr ι b hb U ⟨trackCycle threeInFive,hg⟩
  change conditionalHom U ((trackCycle threeInFive).viaEmbedding ι) ∈ _ at h
  rw [trackCycle_viaEmbedding] at h
  have hs : threeInFive.trans ι = s := Function.Embedding.ext he
  simpa only [hs] using h

noncomputable def offsetFrame {m n : ℕ} (s : Fin n ↪ Fin m) (b : Fin m)
    (u : Fin n → CutRing × CutRing) : Fin m → CutRing × CutRing :=
  ∑ i, (Pi.single (s i) (u i) - Pi.single b (u i))

theorem offsetFrame_apply {m n : ℕ} (s : Fin n ↪ Fin m) (b : Fin m)
    (hb : b ∉ Set.range s) (u : Fin n → CutRing × CutRing) (i : Fin n) :
    offsetFrame s b u (s i) = u i := by
  classical
  have hbi : s i ≠ b := fun h => hb ⟨i,h⟩
  simp only [offsetFrame,Finset.sum_apply,Pi.sub_apply,Pi.single_apply, hbi,ite_false,sub_zero]
  have he : (∑ j : Fin n, if s i = s j then u j else 0) = u i := by
    simp only [s.injective.eq_iff]
    simp
  exact he

theorem offsetFrame_generated (a : ℕ) (r : CutRing) (m n : ℕ)
    (s : Fin n ↪ Fin (m+1)) (b : Fin (m+1)) (u : Fin n → CutRing × CutRing) :
    trackTranslation (a := a) (offsetFrame s b u) ∈ sourceGenerated a r m := by
  classical
  unfold offsetFrame
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [trackTranslation_zero]
  | @insert i t hi ih =>
      rw [Finset.sum_insert hi,trackTranslation_add]
      exact (sourceGenerated a r m).mul_mem (balanced_difference_generated a r m b (s i) (u i)) ih

theorem distinct_track_cycle_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1)
    (U : polygonAlgebra a) (s : Fin 3 → Fin (m+1) × (CutRing × CutRing))
    (ht : Function.Injective (fun i => (s i).1))
    (hs : Function.Injective (SlotMap a (m+1) U s)) :
    slotHom U s hs (trackCycle (Function.Embedding.refl _)) ∈ sourceGenerated a r m := by
  classical
  let ι : Fin 3 ↪ Fin (m+1) := ⟨fun i => (s i).1,ht⟩
  obtain ⟨b,c,_,hb,_⟩ := two_spare_tracks (by omega : 5 ≤ m+1) ι
  have hb' : b ∉ Set.range ι := by rintro ⟨i,hi⟩; exact hb i hi
  let d := offsetFrame ι b (fun i => (s i).2)
  have hd := offsetFrame_generated a r m 3 ι b (fun i => (s i).2)
  have heq : trackTranslation (a := a) d * conditionalHom U (trackCycle ι) *
      (trackTranslation d)⁻¹ = slotHom U s hs (trackCycle (Function.Embedding.refl _)) := by
    have he (i : Fin 3) (x : U.val) :
        (trackTranslation (a := a) d).val (ι i,x.val) = SlotMap a (m+1) U s (i,x) := by
      change (ι i,translate a (d (ι i)) x.val) = _
      dsimp only [d]
      rw [offsetFrame_apply ι b hb']
      rfl
    apply Subtype.ext
    apply Equiv.ext
    intro y
    obtain ⟨p,rfl⟩ := (trackTranslation (a := a) d).val.surjective y
    change (trackTranslation (a := a) d).val
      (conditionalPerm U (trackCycle ι) ((trackTranslation d).val.symm ((trackTranslation d).val p))) = _
    rw [Equiv.symm_apply_apply]
    by_cases hx : p.2 ∈ U.val
    · by_cases hi : p.1 ∈ Set.range ι
      · obtain ⟨i,hi⟩ := hi
        obtain ⟨j,x⟩ := p
        dsimp at hx hi
        subst j
        change (trackTranslation (a := a) d).val
          (if x ∈ U.val then trackCycle ι (ι i) else ι i,x) = _
        simp only [hx,ite_true,trackCycle_apply]
        rw [he (i+1) ⟨x,hx⟩,he i ⟨x,hx⟩]
        change _ = slotPerm U s hs _ _
        rw [slotPerm_apply]
        have hz := trackCycle_apply (Function.Embedding.refl (Fin 3)) i
        change trackCycle (Function.Embedding.refl (Fin 3)) i = i+1 at hz
        rw [hz]
      · have hf : conditionalPerm U (trackCycle ι) p = p := by
          simp [conditionalPerm,trackCycle_apply_of_notMem ι hi]
        rw [hf]
        symm
        apply slotPerm_apply_of_notMem
        rintro ⟨⟨i,x⟩,hi'⟩
        rw [← he] at hi'
        have hh := (trackTranslation (a := a) d).val.injective hi'
        exact hi ⟨i,congrArg Prod.fst hh⟩
    · have hf : conditionalPerm U (trackCycle ι) p = p := by
        change (if p.2 ∈ U.val then trackCycle ι p.1 else p.1,p.2) = p
        simp only [hx,ite_false]
      rw [hf]
      symm
      apply slotPerm_apply_of_notMem
      rintro ⟨⟨i,x⟩,hi'⟩
      rw [← he] at hi'
      have hh := (trackTranslation (a := a) d).val.injective hi'
      exact hx (congrArg Prod.snd hh ▸ x.property)
  rw [← heq]
  exact (sourceGenerated a r m).mul_mem
    ((sourceGenerated a r m).mul_mem hd (conditional_cycle_generated a r m hr hm U ι))
    ((sourceGenerated a r m).inv_mem hd)

private def starThreeInFive (i : Fin 3) : Fin 3 ↪ Fin 5 :=
  ⟨![threeInFive i,3,4],by fin_cases i <;> decide⟩

private theorem star_cycle_identity :
    trackCycle (starThreeInFive 0) * trackCycle (starThreeInFive 1) *
      trackCycle (starThreeInFive 2) * trackCycle (starThreeInFive 0) *
      trackCycle (starThreeInFive 1) = trackCycle threeInFive := by decide

theorem threeSlot_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1)
    (g : polygonFullGroup a (m+1)) (hg : IsThreeSlotCycle g) :
    g ∈ sourceGenerated a r m := by
  obtain ⟨U,s,hs,rfl⟩ := threeSlot_eq_slotHom hg
  obtain ⟨k,l,hkl,hk,hl⟩ := two_spare_tracks (by omega : 5 ≤ m+1) (fun i => (s i).1)
  let S := extendSlots s k l
  have hS := extendSlots_injective U s hs k l hkl hk hl
  let φ := slotHom U S hS
  have hi (i : Fin 3) : φ (trackCycle (starThreeInFive i)) ∈ sourceGenerated a r m := by
    rw [slotHom_subcycle]
    apply distinct_track_cycle_generated a r m hr hm
    intro j n he
    fin_cases i <;> fin_cases j <;> fin_cases n
    all_goals dsimp [S,starThreeInFive,extendSlots,threeInFive] at he
    all_goals first | rfl | exact False.elim (hkl he) | exact False.elim (hkl he.symm) |
      exact False.elim (hk _ he) | exact False.elim (hl _ he) |
      exact False.elim (hk _ he.symm) | exact False.elim (hl _ he.symm)
  have h := (sourceGenerated a r m).mul_mem
    ((sourceGenerated a r m).mul_mem ((sourceGenerated a r m).mul_mem
      ((sourceGenerated a r m).mul_mem (hi 0) (hi 1)) (hi 2)) (hi 0)) (hi 1)
  simp only [← map_mul,star_cycle_identity] at h
  rw [slotHom_subcycle] at h
  have he : S ∘ threeInFive = s := funext (extendSlots_three s k l)
  simpa only [he] using h

theorem sourceGenerated_eq_alternating (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1) :
    sourceGenerated a r m = polygonAlternatingGroup a (m+1) := by
  apply le_antisymm (sourceGenerated_le_alternating a r m (by omega))
  apply (Subgroup.closure_le _).mpr
  exact threeSlot_generated a r m hr hm

theorem polygonAlternatingGroup_fg (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1) :
    Group.FG (polygonAlternatingGroup a (m+1)) := by
  rw [← sourceGenerated_eq_alternating a r m hr hm]
  unfold sourceGenerated
  have : Finite (Set.range (sourceGenerator a r m)) := (Set.finite_range _).to_subtype
  infer_instance

theorem alternatingGenerator_surjective (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1)
    (hm' : 2 ≤ m) : Function.Surjective (FreeGroup.lift (alternatingGenerator a r m hm')) := by
  rw [FreeGroup.lift_surjective_iff_closure_range_eq_top]
  apply Subgroup.map_injective (polygonAlternatingGroup a (m+1)).subtype_injective
  rw [← MonoidHom.range_eq_map,Subgroup.range_subtype,MonoidHom.map_closure]
  have he : (polygonAlternatingGroup a (m+1)).subtype ''
      Set.range (alternatingGenerator a r m hm') = Set.range (sourceGenerator a r m) := by
    rw [← Set.range_comp]
    rfl
  rw [he]
  exact sourceGenerated_eq_alternating a r m hr hm

theorem sourceCover_surjective (a : ℕ) (r : CutRing) (m L : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1) (hm' : 2 ≤ m) :
    Function.Surjective (coverMap L (alternatingGenerator a r m hm')) :=
  coverMap_surjective L _ (alternatingGenerator_surjective a r m hr hm hm')

theorem sourceCover_eventually_perfect (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1) (hm' : 2 ≤ m) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      Group.IsPerfect (BoundedRelationCover M (alternatingGenerator a r m hm')) := by
  let := polygonAlternatingGroup_perfect a (m+1) (by omega)
  exact bounded_cover_eventually_perfect _ (alternatingGenerator_surjective a r m hr hm hm')

end GenuineFiniteGeneration

end SimpleAmenable
end
end

end OAI
