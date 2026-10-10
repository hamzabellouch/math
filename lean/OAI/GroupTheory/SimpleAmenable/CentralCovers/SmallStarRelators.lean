import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.TemplateFormalRelators

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SmallStarRelators
variable {α ι Ω H Q : Type*} [Fintype α] [DecidableEq α] [Group H] [Group Q]
    [Group.IsPerfect (alternatingGroup α)]

noncomputable def alphabetStarLift (I : FiveAlphabet α) (s : alternatingGroup I.val) :
    TrackStar α := universalMap (subtypeAlternatingHom I.val)
      (Classical.choose (universalProjection_surjective (alternatingGroup I.val) s))

@[simp] theorem alphabetStarLift_projection (I : FiveAlphabet α) (s : alternatingGroup I.val) :
    universalProjection (alternatingGroup α) (alphabetStarLift I s)=subtypeAlternatingHom I.val s := by
  have h := DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom I.val))
    (Classical.choose (universalProjection_surjective (alternatingGroup I.val) s))
  simpa only [MonoidHom.comp_apply,alphabetStarLift,
    Classical.choose_spec (universalProjection_surjective (alternatingGroup I.val) s)] using h

noncomputable def smallFamilyStarWord : SmallFamilyWord α ι →*
    FreeGroup (Option ι × TrackStar α) :=
  FreeGroup.lift (fun l => FreeGroup.of (l.2.1,alphabetStarLift l.1 l.2.2))

theorem smallFamilyStarWord_model :
    (formalAssignmentEval (ι := ι) (universalProjection (alternatingGroup α))).comp
      smallFamilyStarWord =
    smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}) := by
  apply FreeGroup.ext_hom
  rintro ⟨I,i,s⟩
  change formalAssignmentEval (universalProjection (alternatingGroup α))
      (FreeGroup.of (i,alphabetStarLift I s)) = _
  ext σ
  cases i with
  | none => simp [formalAssignmentEval,assignmentEval,copySourceMap,maskFamily,sectorMask,smallFamilyModel]
  | some i =>
    cases hi : σ i <;>
      simp [formalAssignmentEval,assignmentEval,copySourceMap,maskFamily,sectorMask,smallFamilyModel,hi]

theorem smallFamilyStarWord_eval (F : Option ι → TrackStar α →* H)
    (f : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hspec : ∀ I i, (F i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val))) :
    (copyFamilyEval F).comp smallFamilyStarWord=smallFamilyEval f := by
  apply FreeGroup.ext_hom
  rintro ⟨I,i,s⟩
  have h := DFunLike.congr_fun (hspec I i)
    (Classical.choose (universalProjection_surjective (alternatingGroup I.val) s))
  simpa only [MonoidHom.comp_apply,smallFamilyStarWord,FreeGroup.lift_apply_of,
    copyFamilyEval_of,smallFamilyEval_of,alphabetStarLift,
    Classical.choose_spec (universalProjection_surjective (alternatingGroup I.val) s)] using h

theorem smallFamilyStarWord_supported
    (L : Finset α → Subgroup H) (hmono : Monotone L)
    (F : Option ι → TrackStar α →* H) (hF : ∀ i, SmallSupported L (F i))
    (S : Finset α) (w : SmallFamilyWord α ι) (hw : w ∈ smallFamilyLocal S) :
    copyFamilyEval F (smallFamilyStarWord w) ∈ L S := by
  have hle : smallFamilyLocal (ι := ι) S ≤ (L S).comap
      ((copyFamilyEval F).comp smallFamilyStarWord) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨⟨I,i,s⟩,hI,rfl⟩
    let J : ControlAlphabet α := ⟨I.val,by have hi := I.property.2; omega,
      by have hi := I.property.2; omega⟩
    apply hmono hI
    apply hF i J
    refine ⟨Classical.choose (universalProjection_surjective (alternatingGroup I.val) s),?_⟩
    simp [smallFamilyStarWord,alphabetStarLift,J]
  exact hle hw

theorem template_supported_word_controls
    (L : Finset α → Subgroup H) (hmono : Monotone L) (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
    {q : H →* Q} {v : (Ω → alternatingGroup α) →* Q} (T : ActualLawfulTable q v)
    (U : ι → Set Ω) (V : Set Ω)
    (hT : ∀ i : Option ι, SmallSupported L (T.sector (templateSides U V i)))
    (f : TrackStar α →* H) (hf : SmallSupported L f)
    (hcontrol : SmallControlled c f (T.sector V))
    (S : Finset α) (hS : S.card+10 ≤ Fintype.card α)
    (w : SmallFamilyWord α ι) (hw : w ∈ smallFamilyLocal S)
    (hrel : smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}) w=1) :
    ∀ x ∈ f.range, Commute
      (copyFamilyEval (fun i => T.sector (templateSides U V i)) (smallFamilyStarWord w)) x := by
  have hm : formalAssignmentEval (universalProjection (alternatingGroup α))
      (smallFamilyStarWord w)=1 := by
    have h := DFunLike.congr_fun (smallFamilyStarWord_model (α := α) (ι := ι)) w
    exact h.trans hrel
  have hz := T.template_relator_central U V _ hm
  exact small_control_transfer L c hc hd f (T.sector V) hf hcontrol S _
    (smallFamilyStarWord_supported L hmono _ hT S w hw) hS
    (fun J s => show Commute _ (T.sector V (universalMap (subtypeAlternatingHom J.val) s)) from
      (hz _ (T.sector_mem _ _)).symm)

end SmallStarRelators

section CellConstantActions
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem cell_constant_action (hlarge : 20 ≤ m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (U W : polygonAlgebra a)
    (hU : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) U.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) W.val)
    (b : Bool) (he : U ⊓ W = if b then W else ⊥)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.fullGeometricSector (by omega) P h W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)) :
    ∀ x ∈ f.range,
      B.fullGeometricSector (by omega) P h U (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) P h U (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      (if b then B.c (subtypeAlternatingHom I.val (universalProjection _ s)) else 1)*x*
        (if b then B.c (subtypeAlternatingHom I.val (universalProjection _ s)) else 1)⁻¹ := by
  have hspec := DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom I.val)) s
  simp only [MonoidHom.comp_apply] at hspec
  cases b with
  | false =>
    have hh := B.chart_action_transfer hlarge P h U ⊥ W hU
      (fun _ _ _ => Iff.rfl) hW (by simpa using he) f hf hc I s
    simpa only [Bool.false_eq_true,↓reduceIte,B.fullGeometricSector_bot,MonoidHom.one_apply] using hh
  | true =>
    have hh := B.chart_action_transfer hlarge P h U (wholePolygon a) W hU
      (fun _ _ _ => Iff.rfl) hW (by change U ⊓ W=⊤ ⊓ W; simpa using he) f hf hc I s
    simpa only [↓reduceIte,B.fullGeometricSector_whole,MonoidHom.comp_apply,hspec] using hh

theorem cell_restrict_action (hlarge : 20 ≤ m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (U W : polygonAlgebra a)
    (hU : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) U.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) W.val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.fullGeometricSector (by omega) P h W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)) :
    ∀ x ∈ f.range,
      B.fullGeometricSector (by omega) P h U (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) P h U (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.fullGeometricSector (by omega) P h (U ⊓ W) (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) P h (U ⊓ W) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  exact B.chart_action_transfer hlarge P h U (U ⊓ W) W hU
    (fun x y hh => and_congr (hU x y hh) (hW x y hh)) hW
    (by rw [inf_assoc,inf_idem]) f hf hc I s

end InitialCoverSystem
end CellConstantActions

end SimpleAmenable
end
end

end OAI
