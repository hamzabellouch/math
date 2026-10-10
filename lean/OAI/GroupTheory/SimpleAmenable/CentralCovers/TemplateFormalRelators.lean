import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PairControl
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CentralRangeReflection

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TemplateFormalRelators
variable {E H Q Ω ι : Type*} [Group E] [Group H] [Group Q]

noncomputable def maskedAssignmentPullback (r : Ω → ι → Bool) (V : Set Ω) :
    ((ι → Bool) → E) →* (Ω → E) := by
  classical
  exact { toFun := fun f ω => if ω ∈ V then f (r ω) else 1
          map_one' := by ext ω; simp
          map_mul' := by intro f g; ext ω; by_cases h : ω ∈ V <;> simp [h] }

noncomputable def templateSides (U : ι → Set Ω) (V : Set Ω) : Option ι → Set Ω
  | none => V
  | some i => V ∩ U i

noncomputable def templateAssignment (U : ι → Set Ω) (ω : Ω) : ι → Bool := by
  classical
  exact fun i => decide (ω ∈ U i)

theorem template_mask_eval (U : ι → Set Ω) (V : Set Ω) :
    copyFamilyEval (fun j : Option ι => (sectorMask (templateSides U V j)).comp (universalProjection E)) =
      (maskedAssignmentPullback (templateAssignment U) V).comp
        (formalAssignmentEval (universalProjection E)) := by
  classical
  apply FreeGroup.ext_hom
  rintro ⟨j,s⟩
  ext ω
  cases j with
  | none =>
    simp [copyFamilyEval_of,templateSides,formalAssignmentEval,assignmentEval,
      copySourceMap,maskFamily,maskedAssignmentPullback,sectorMask]; rfl
  | some i =>
    by_cases hV : ω ∈ V <;> by_cases hi : ω ∈ U i <;>
      simp [copyFamilyEval_of,templateSides,formalAssignmentEval,assignmentEval,
        copySourceMap,maskFamily,maskedAssignmentPullback,sectorMask,templateAssignment,hV,hi]

namespace ActualLawfulTable
variable [Group.IsPerfect E] {q : H →* Q} {v : (Ω → E) →* Q}
    (T : ActualLawfulTable q v)

theorem template_eval_projection (U : ι → Set Ω) (V : Set Ω) :
    q.comp (copyFamilyEval (fun j : Option ι => T.sector (templateSides U V j))) =
      (v.comp (maskedAssignmentPullback (templateAssignment U) V)).comp
        (formalAssignmentEval (universalProjection E)) := by
  rw [MonoidHom.comp_assoc,← template_mask_eval]
  apply FreeGroup.ext_hom
  rintro ⟨j,s⟩
  simp only [MonoidHom.comp_apply,copyFamilyEval_of]
  exact T.sector_projection_apply _ _

theorem template_relator_central (U : ι → Set Ω) (V : Set Ω)
    (w : FreeGroup (Option ι × UniversalExtension E))
    (hw : formalAssignmentEval (universalProjection E) w=1) :
    copyFamilyEval (fun j : Option ι => T.sector (templateSides U V j)) w ∈
      Subgroup.centralizer (T.carrier : Set H) := by
  let f := copyFamilyEval (fun j : Option ι => T.sector (templateSides U V j))
  have hf : f.range ≤ T.carrier := by
    rw [copyFamilyEval_range]
    apply iSup_le
    rintro i y ⟨s,rfl⟩
    exact T.sector_mem _ _
  have hq : q (f w)=1 := by
    have hh := DFunLike.congr_fun (T.template_eval_projection U V) w
    simpa only [MonoidHom.comp_apply,hw,map_one] using hh
  have hc := T.law (show (⟨f w,hf ⟨w,rfl⟩⟩ : T.carrier) ∈
      (q.comp T.carrier.subtype).ker from hq)
  intro x hx
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨x,hx⟩)

end ActualLawfulTable
end TemplateFormalRelators

section TemplateControlledRelators
variable {E E' S S' H Ω ι : Type*} [Group E] [Group E'] [Group S]
    [Group S'] [Group H]

theorem copyFamilyEval_comp_source (F : Option ι → E →* H) (ψ : E' →* E) :
    (copyFamilyEval F).comp (copySourceMap ψ)=copyFamilyEval (fun i => (F i).comp ψ) := by
  apply FreeGroup.ext_hom
  rintro ⟨i,x⟩
  simp [copySourceMap]

theorem formalAssignmentEval_natural (π : E →* S) (π' : E' →* S')
    (ψ : E' →* E) (ρ : S' →* S) (hπ : π.comp ψ=ρ.comp π') :
    (formalAssignmentEval (ι := ι) π).comp (copySourceMap ψ)=
      (assignmentPost ρ).comp (formalAssignmentEval π') := by
  classical
  apply FreeGroup.ext_hom
  rintro ⟨i,x⟩
  ext σ
  have hx := DFunLike.congr_fun hπ x
  change π (ψ x)=ρ (π' x) at hx
  cases i with
  | none =>
    simpa [formalAssignmentEval,copySourceMap,assignmentEval,maskFamily,sectorMask,
      assignmentPost] using hx
  | some i =>
    cases hi : σ i <;>
      simp [formalAssignmentEval,copySourceMap,assignmentEval,maskFamily,sectorMask,
        assignmentPost,hi,hx]

variable {α Q : Type*} [Fintype α] [DecidableEq α] [Group Q]
    [Group.IsPerfect (alternatingGroup α)]

theorem template_small_relator_controls
    (L : Finset α → Subgroup H) (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
    (hα : 20 ≤ Fintype.card α)
    {q : H →* Q} {v : (Ω → alternatingGroup α) →* Q} (T : ActualLawfulTable q v)
    (U : ι → Set Ω) (V : Set Ω)
    (hT : ∀ i : Option ι, SmallSupported L (T.sector (templateSides U V i)))
    (f : TrackStar α →* H) (hf : SmallSupported L f)
    (hcontrol : SmallControlled c f (T.sector V))
    (I : ControlAlphabet α) (w : FreeGroup (Option ι × UniversalExtension (alternatingGroup I.val)))
    (hw : formalAssignmentEval (universalProjection (alternatingGroup I.val)) w=1) :
    ∀ x ∈ f.range, Commute
      (copyFamilyEval (fun i : Option ι => (T.sector (templateSides U V i)).comp
        (universalMap (subtypeAlternatingHom I.val))) w) x := by
  let ψ := universalMap (subtypeAlternatingHom I.val)
  let F := fun i : Option ι => T.sector (templateSides U V i)
  let u := copyFamilyEval (fun i => (F i).comp ψ) w
  have hu : u ∈ L I.val := by
    have he : (copyFamilyEval (fun i => (F i).comp ψ)).range ≤ L I.val := by
      rw [copyFamilyEval_range]
      apply iSup_le
      intro i
      exact hT i I
    exact he ⟨w,rfl⟩
  have he : u=copyFamilyEval F (copySourceMap ψ w) :=
    (DFunLike.congr_fun (copyFamilyEval_comp_source F ψ) w).symm
  have hw' : formalAssignmentEval (universalProjection (alternatingGroup α))
      (copySourceMap ψ w)=1 := by
    have hh := DFunLike.congr_fun (formalAssignmentEval_natural
      (universalProjection (alternatingGroup α)) (universalProjection (alternatingGroup I.val))
      ψ (subtypeAlternatingHom I.val) (universalMap_spec _)) w
    simpa only [MonoidHom.comp_apply,hw,map_one] using hh
  have hz : u ∈ Subgroup.centralizer (T.carrier : Set H) := by
    rw [he]
    exact T.template_relator_central U V _ hw'
  exact small_control_transfer L c hc hd f (T.sector V) hf hcontrol I.val u hu
    (by have hh := I.property.2; omega)
    (fun J s => show Commute u (T.sector V (universalMap (subtypeAlternatingHom J.val) s)) from
      (hz _ (T.sector_mem _ _)).symm)

end TemplateControlledRelators

end SimpleAmenable
end
end

end OAI
