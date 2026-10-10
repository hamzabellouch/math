import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.TemplateRelators
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalLaws

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TemplateActualRelators
variable {E H Q ι Ω : Type*} [Group E] [Group H] [Group Q] [Group.IsPerfect E]
namespace ActualLawfulTable
variable {q : H →* Q} {v : (Ω → E) →* Q} (T : ActualLawfulTable q v)

theorem template_relator_central_on (U : ι → Set Ω) (V : Set Ω)
    (w : FreeGroup (Option ι × UniversalExtension E))
    (hw : ∀ ω ∈ V, formalAssignmentEval (universalProjection E) w (templateAssignment U ω)=1) :
    copyFamilyEval (fun j : Option ι => T.sector (templateSides U V j)) w ∈
      Subgroup.centralizer (T.carrier : Set H) := by
  let f := copyFamilyEval (fun j : Option ι => T.sector (templateSides U V j))
  have hf : f.range ≤ T.carrier := by
    rw [copyFamilyEval_range]
    apply iSup_le
    rintro i y ⟨s,rfl⟩
    exact T.sector_mem _ _
  have hm : maskedAssignmentPullback (templateAssignment U) V
      (formalAssignmentEval (universalProjection E) w)=1 := by
    classical
    ext ω
    change (if ω ∈ V then _ else 1)=1
    split_ifs with hω
    · exact hw ω hω
    · rfl
  have hq : q (f w)=1 := by
    have hh := DFunLike.congr_fun (T.template_eval_projection U V) w
    simpa only [MonoidHom.comp_apply,hm,map_one] using hh
  have hc := T.law (show (⟨f w,hf ⟨w,rfl⟩⟩ : T.carrier) ∈
      (q.comp T.carrier.subtype).ker from hq)
  intro x hx
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨x,hx⟩)

end ActualLawfulTable
end TemplateActualRelators

section TemplateSupportedActualRelators
variable {α H Q ι Ω : Type*} [Fintype α] [DecidableEq α] [Group H] [Group Q]
    [Group.IsPerfect (alternatingGroup α)]

theorem template_supported_word_controls_on
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
    (hrel : ∀ ω ∈ V, smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}) w
      (templateAssignment U ω)=1) :
    ∀ x ∈ f.range, Commute
      (copyFamilyEval (fun i => T.sector (templateSides U V i)) (smallFamilyStarWord w)) x := by
  have hm : ∀ ω ∈ V, formalAssignmentEval (universalProjection (alternatingGroup α))
      (smallFamilyStarWord w) (templateAssignment U ω)=1 := by
    intro ω hω
    have he := DFunLike.congr_fun (smallFamilyStarWord_model (α := α) (ι := ι)) w
    exact (congrFun he (templateAssignment U ω)).trans (hrel ω hω)
  have hz := T.template_relator_central_on U V _ hm
  exact small_control_transfer L c hc hd f (T.sector V) hf hcontrol S _
    (smallFamilyStarWord_supported L hmono _ hT S w hw) hS
    (fun J s => show Commute _ (T.sector V (universalMap (subtypeAlternatingHom J.val) s)) from
      (hz _ (T.sector_mem _ _)).symm)

end TemplateSupportedActualRelators

section ActualTemplateActualWords

theorem smallActualRelator_at {a : ℕ} {α ι : Type*} [Fintype α] [DecidableEq α]
    (R : ι → polygonAlgebra a) (w : SmallFamilyWord α ι)
    (hw : smallFamilyModel (actualTestMask R) w=1)
    (σ : ι → Bool) (hσ : σ ∈ Set.range (polygonAssignment R)) :
    smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}) w σ=1 := by
  rw [smallActualModel_pullback] at hw
  exact congrFun hw ⟨σ,hσ⟩

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem actual_template_actual_word_controls (hlarge : 25 ≤ m+1)
    (P : κ → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (U : ι → polygonAlgebra a) (V : polygonAlgebra a)
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) P j).val) (U i).val)
    (hV : ResolvedBy (fun j => (primitiveTests (a := a) (r := r) P j).val) V.val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.fullGeometricSector (by omega) P h V))
    (S : Finset (Fin (m+1))) (hS : S.card ≤ 15)
    (w : SmallFamilyWord (Fin (m+1)) ι) (hw : w ∈ smallFamilyLocal S)
    (R : ι → polygonAlgebra a)
    (hreal : ∀ x ∈ V.val, polygonAssignment U x ∈ Set.range (polygonAssignment R))
    (hrel : smallFamilyModel (actualTestMask R) w=1) :
    ∀ x ∈ f.range, Commute
      (copyFamilyEval (fun i => B.fullGeometricSector (by omega) P h (marginFamily U V i))
        (smallFamilyStarWord w)) x := by
  let masks := fun W : polygonAlgebra a => resolvedPolygonMask
    (primitiveTests (a := a) (r := r) P) W.val
  have he (i : Option ι) : masks (marginFamily U V i)=templateSides (fun i => masks (U i)) (masks V) i := by
    cases i with
    | none => rfl
    | some i => exact resolvedPolygonMask_inter _ V.val (U i).val hV (hU i)
  have hs i : SmallSupported (sourceAlignedGroup a r m hm M B.t)
      ((B.fullPrimitiveTable (by omega) P h).sector
        (templateSides (fun i => masks (U i)) (masks V) i)) := by
    rw [← he i]
    apply B.fullGeometricSector_supported
    cases i with
    | none => exact hV
    | some i => exact fun x y hh => and_congr (hV x y hh) (hU i x y hh)
  have hm : ∀ ω ∈ masks V,
      smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}) w
        (templateAssignment (fun i => masks (U i)) ω)=1 := by
    rintro ⟨σ,x,rfl⟩ hx
    have hxV := (resolvedPolygonMask_mem _ V.val hV x).mp hx
    have he : templateAssignment (fun i => masks (U i))
        ⟨polygonAssignment (primitiveTests (a := a) (r := r) P) x,⟨x,rfl⟩⟩=
        polygonAssignment U x := by
      funext i
      apply decide_eq_decide.mpr
      exact resolvedPolygonMask_mem _ (U i).val (hU i) x
    rw [he]
    exact smallActualRelator_at R w hrel _ (hreal x hxV)
  have hh := template_supported_word_controls_on _ (sourceAlignedGroup_mono B.t)
    B.c B.constant_aligned B.disjoint_aligned (B.fullPrimitiveTable (by omega) P h)
    (fun i => masks (U i)) (masks V) hs f hf hc S (by simp only [Fintype.card_fin]; omega)
    w hw hm
  have heval : (fun i => B.fullGeometricSector (by omega) P h (marginFamily U V i))=
      (fun i => (B.fullPrimitiveTable (by omega) P h).sector
        (templateSides (fun i => masks (U i)) (masks V) i)) := by
    funext i
    exact congrArg ((B.fullPrimitiveTable (by omega) P h).sector) (he i)
  rw [heval]
  exact hh

end InitialCoverSystem
end ActualTemplateActualWords

end SimpleAmenable
end
end

end OAI
