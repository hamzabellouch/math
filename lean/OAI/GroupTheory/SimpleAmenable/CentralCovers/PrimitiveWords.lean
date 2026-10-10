import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveCopies
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CommonTranslatedCopies
import OAI.GroupTheory.SimpleAmenable.Arithmetic.CompiledTranslations
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ConditionalFamilyLaws

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PrimitiveWords

abbrev SmallAlt (m : ℕ) := {s : alternatingGroup (Fin (m+1)) // s.val.support.card ≤ 5}

theorem smallAlt_free_surjective (m : ℕ) :
    Function.Surjective (FreeGroup.lift (fun s : SmallAlt m => s.val)) := by
  apply MonoidHom.range_eq_top.mp
  rw [FreeGroup.range_lift_eq_closure]
  apply top_unique
  rw [← alternatingGroup.closure_isThreeCycles_eq_top]
  apply Subgroup.closure_mono
  intro s hs
  exact ⟨⟨s,by rw [hs.card_support]; omega⟩,rfl⟩

noncomputable def smallAltWord {m : ℕ} (s : alternatingGroup (Fin (m+1))) :
    FreeGroup (SmallAlt m) := (smallAlt_free_surjective m s).choose

@[simp] theorem smallAltWord_eval {m : ℕ} (s : alternatingGroup (Fin (m+1))) :
    FreeGroup.lift (fun t : SmallAlt m => t.val) (smallAltWord s) = s :=
  (smallAlt_free_surjective m s).choose_spec

noncomputable def conditionalWord {m : ℕ} (j : Fin 5)
    (s : alternatingGroup (Fin (m+1))) : FreeGroup (SourceGeneratorLabel m) :=
  FreeGroup.map (fun t : SmallAlt m => sourceConditionalLabel m
    (j,⟨t.val.val,t.val.property,t.property⟩)) (smallAltWord s)

theorem conditionalWord_eval {m : ℕ} {H : Type*} [Group H]
    (f : SourceGeneratorLabel m → H) (h : alternatingGroup (Fin (m+1)) →* H)
    (j : Fin 5) (hj : ∀ t : SmallAlt m,
      f (sourceConditionalLabel m (j,⟨t.val.val,t.val.property,t.property⟩)) = h t.val)
    (s : alternatingGroup (Fin (m+1))) : FreeGroup.lift f (conditionalWord j s) = h s := by
  have he : (FreeGroup.lift f).comp (FreeGroup.map (fun t : SmallAlt m =>
      sourceConditionalLabel m (j,⟨t.val.val,t.val.property,t.property⟩))) =
      h.comp (FreeGroup.lift (fun t : SmallAlt m => t.val)) := by
    apply FreeGroup.ext_hom
    intro t
    simpa only [MonoidHom.comp_apply, FreeGroup.map.of,FreeGroup.lift_apply_of] using hj t
  simpa only [MonoidHom.comp_apply,conditionalWord,smallAltWord_eval] using
    DFunLike.congr_fun he (smallAltWord s)

noncomputable def primitiveWord {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I)
    (p : Fin 5 × (CutRing × CutRing)) (s : alternatingGroup I) :
    FreeGroup (SourceGeneratorLabel m) :=
  let k := (commonFrame a r m hm I b hb p.2).k
  latticeWord k * conditionalWord p.1 (subtypeAlternatingHom I s) * (latticeWord k)⁻¹

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem conditionalWord_mk (j : Fin 5) (s : alternatingGroup (Fin (m+1))) :
    PresentedGroup.mk (shortRelations M (alternatingGenerator a r m hm)) (conditionalWord j s) =
      B.initialConditional j s := by
  have he : FreeGroup.lift (PresentedGroup.of : SourceGeneratorLabel m →
      BoundedRelationCover M (alternatingGenerator a r m hm)) =
      PresentedGroup.mk (shortRelations M (alternatingGenerator a r m hm)) := by
    ext i
    rfl
  rw [← he]
  exact conditionalWord_eval _ (B.initialConditional j) j
    (fun t => (B.initialConditional_input j t.val t.property).symm) s

theorem primitiveWord_mk (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I)
    (p : Fin 5 × (CutRing × CutRing)) (s : alternatingGroup I) :
    PresentedGroup.mk (shortRelations M (alternatingGenerator a r m hm))
        (primitiveWord (a := a) (r := r) (hm := hm) I b hb p s) = B.primitiveCopy I b hb p s := by
  simp only [primitiveWord,map_mul,map_inv,B.latticeWord_mk,B.conditionalWord_mk]
  rfl

end InitialCoverSystem

theorem primitiveWord_eval {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I)
    (p : Fin 5 × (CutRing × CutRing)) (s : alternatingGroup I) :
    FreeGroup.lift (alternatingGenerator a r m hm)
        (primitiveWord (a := a) (r := r) (hm := hm) I b hb p s) =
      conditionalAlternatingHom (spatialTranslate p.2 (initialTest a r p.1))
        (subtypeAlternatingHom I s) := by
  have ht : ∀ i, sourceLatticeMap a r m hm (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
      alternatingGenerator a r m hm (sourceTranslationLabel m i) := by
    intro i
    exact commutingFamilyHom_of _ _ i
  rw [primitiveWord,map_mul,map_mul,map_inv,latticeWord_eval _ _ ht]
  rw [conditionalWord_eval _ (conditionalAlternatingHom (initialTest a r p.1)) p.1
    (fun _ => rfl)]
  exact (commonFrame a r m hm I b hb p.2).conditional_projection _ s

end PrimitiveWords

section PrimitiveFamilyLaws

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {ι : Type*}

noncomputable def primitiveFamilyTests (P : ι → Fin 5 × (CutRing × CutRing)) :
    Option ι → polygonAlgebra a
  | none => wholePolygon a
  | some i => spatialTranslate (P i).2 (initialTest a r (P i).1)

namespace InitialCoverSystem

variable (B : InitialCoverSystem a r m hm M)

noncomputable def primitiveFamily (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing)) :
    Option ι → alternatingGroup I →* BoundedRelationCover M (alternatingGenerator a r m hm)
  | none => B.initialAlphabet I 0
  | some i => B.primitiveCopy I b hb (P i)

def PrimitiveFamilyLaw (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing)) : Prop :=
  CentralOn (coverMap M (alternatingGenerator a r m hm))
    (copyFamilyEval (B.primitiveFamily I b hb P)).range

theorem primitiveFamily_projection (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing)) (i : Option ι) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.primitiveFamily I b hb P i) =
      (conditionalAlternatingHom (primitiveFamilyTests (a := a) (r := r) P i)).comp (subtypeAlternatingHom I) := by
  cases i with
  | none =>
    rw [primitiveFamily,initialAlphabet,← MonoidHom.comp_assoc,
      B.initialConditional_projection]
    rfl
  | some i => exact B.primitiveCopy_projection I b hb (P i)

end InitialCoverSystem

noncomputable def primitiveFamilyWord (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing)) :
    Option ι × alternatingGroup I → FreeGroup (SourceGeneratorLabel m)
  | (none,s) => conditionalWord 0 (subtypeAlternatingHom I s)
  | (some i,s) => primitiveWord (a := a) (r := r) (hm := hm) I b hb (P i) s

theorem primitiveFamilyWord_eval (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (i : Option ι × alternatingGroup I) :
    FreeGroup.lift (alternatingGenerator a r m hm)
        (primitiveFamilyWord (a := a) (r := r) (hm := hm) I b hb P i) =
      conditionalAlternatingHom (primitiveFamilyTests (a := a) (r := r) P i.1) (subtypeAlternatingHom I i.2) := by
  rcases i with ⟨i,s⟩
  cases i with
  | none =>
    exact conditionalWord_eval _ (conditionalAlternatingHom (initialTest a r 0)) 0
      (fun _ => rfl) _
  | some i => exact primitiveWord_eval I b hb (P i) s

namespace InitialCoverSystem

variable (B : InitialCoverSystem a r m hm M)

theorem primitiveFamilyWord_mk (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (i : Option ι × alternatingGroup I) :
    PresentedGroup.mk (shortRelations M (alternatingGenerator a r m hm))
        (primitiveFamilyWord (a := a) (r := r) (hm := hm) I b hb P i) =
      B.primitiveFamily I b hb P i.1 i.2 := by
  rcases i with ⟨i,s⟩
  cases i with
  | none => exact B.conditionalWord_mk 0 (subtypeAlternatingHom I s)
  | some i => exact B.primitiveWord_mk I b hb (P i) s

end InitialCoverSystem

theorem primitiveFamilyLaw_eventually [Finite ι]
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm' : 15 ≤ m+1)
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I)
    (P : ι → Fin 5 × (CutRing × CutRing)) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
      B.PrimitiveFamilyLaw I b hb P := by
  let U := primitiveFamilyTests (a := a) (r := r) P
  let input : Option ι × alternatingGroup I →
      (Set.range (polygonAssignment U) → alternatingGroup (Fin (m+1))) :=
    fun i => polygonTableInput U i.1 (subtypeAlternatingHom I i.2)
  obtain ⟨L,hL⟩ := finite_table_with_inputs_eventually (alternatingGenerator a r m hm)
    (actualPolygonTableHom U) input (primitiveFamilyWord (a := a) (r := r) (hm := hm) I b hb P)
    (fun i => (primitiveFamilyWord_eval I b hb P i).trans
      (actualPolygonTableHom_input U i.1 (subtypeAlternatingHom I i.2)).symm)
    (alternatingGenerator_surjective a r m hr hm' hm)
  refine ⟨L,fun M hM B => ?_⟩
  obtain ⟨ρ,hρ,hin⟩ := hL M hM
  have hc : CentralOn (coverMap M (alternatingGenerator a r m hm)) ρ.range := by
    apply centralOn_of_table
    rw [hρ]
    exact actualPolygonTableHom_injective U
  apply hc.mono
  rw [copyFamilyEval_range]
  apply iSup_le
  rintro i y ⟨s,rfl⟩
  refine ⟨input (i,s),?_⟩
  rw [hin,B.primitiveFamilyWord_mk]

end PrimitiveFamilyLaws

end SimpleAmenable
end
end

end OAI
