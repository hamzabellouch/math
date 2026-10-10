import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GrowthAxisUniform

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PairControl
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ i j I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (primitivePair P i j))

noncomputable def pairContainer (i : ι) (positive : Bool) :
    TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (primitivePair P i i) (h i i)
    (if positive then primitiveTests (a := a) (r := r) P i
      else (primitiveTests (a := a) (r := r) P i)ᶜ)

omit [Finite ι] in
theorem pairContainer_eq (i j : ι) (positive : Bool) :
    B.pairContainer hlarge P h i positive =
    B.fullGeometricSector hlarge (primitivePair P i j) (h i j)
      (if positive then primitiveTests (a := a) (r := r) P i
        else (primitiveTests (a := a) (r := r) P i)ᶜ) := by
  apply B.fullGeometricSector_shared_primitive hlarge (primitivePair P i i) (primitivePair P i j) false false rfl _ _ _
  cases positive with
  | false => exact fun x y he => not_congr (resolved_test _ () x y he)
  | true => exact resolved_test _ ()

omit [Finite ι] in
theorem pairContainer_supported (i : ι) (positive : Bool) :
    B.AlignedSmallSupported (B.pairContainer hlarge P h i positive) := by
  apply B.fullGeometricSector_supported
  cases positive with
  | false => exact fun x y he => not_congr (primitivePair_left_resolved P i i x y he)
  | true => exact primitivePair_left_resolved P i i

omit [Finite ι] in
theorem pairSplit_control (i : ι) (j : Option ι) (positive : Bool) :
    SmallControlled B.c (B.pairSplit hlarge P h i j positive)
      (B.pairContainer hlarge P h i positive) := by
  rw [B.pairContainer_eq hlarge P h i (j.getD i) positive]
  exact B.fullGeometricSector_small_control hlarge _ _ _ _ inf_le_right

omit [Finite ι] in
theorem pairContainer_commute (i : ι) (s t : TrackStar (Fin (m+1))) :
    Commute (B.pairContainer hlarge P h i true s) (B.pairContainer hlarge P h i false t) := by
  apply B.fullGeometricSector_commute hlarge _ _ _ _ (primitivePair_left_resolved P i i)
  exact Set.disjoint_left.mpr (by intro x hx hy; exact hy hx)

omit [Finite ι] in
theorem pairSplit_commute (h20 : 20 ≤ m+1) (i : ι) (j k : Option ι)
    (s t : TrackStar (Fin (m+1))) :
    Commute (B.pairSplit hlarge P h i j true s) (B.pairSplit hlarge P h i k false t) :=
  small_control_disjoint _ B.c B.constant_aligned B.disjoint_aligned (by simpa using h20)
    _ _ _ _ (B.pairSplit_supported hlarge P h i j true)
    (B.pairSplit_supported hlarge P h i k false)
    (B.pairContainer_supported hlarge P h i true)
    (B.pairSplit_control hlarge P h i j true)
    (B.pairSplit_control hlarge P h i k false)
    (B.pairContainer_commute hlarge P h i) s t

omit [Finite ι] in

theorem pairStar_small (I : FiveAlphabet (Fin (m+1))) (j : Option ι) :
    (B.pairStar hlarge P h j).comp (universalMap (subtypeAlternatingHom I.val)) =
      (B.smallPrimitiveInputs hlarge P I j).comp
        (universalProjection (alternatingGroup I.val)) := by
  cases j with
  | none =>
    change (B.c.comp (universalProjection (alternatingGroup (Fin (m+1))))).comp _ =
      (B.initialAlphabet I.val 0).comp _
    rw [MonoidHom.comp_assoc,universalMap_spec,← MonoidHom.comp_assoc,B.initialAlphabet_zero]
  | some i =>
    let b := smallAlphabetBalance hlarge I.val (by rw [I.property.2]; omega)
    have hb := smallAlphabetBalance_notMem hlarge I.val (by rw [I.property.2]; omega)
    change (B.fullGeometricSector hlarge (primitivePair P i i) (h i i)
      (primitiveTests (a := a) (r := r) P i)).comp _ = _
    rw [B.fullGeometricSector_inclusion hlarge _ _ I.val (by rw [I.property.2]) b hb
      (h i i I.val (by rw [I.property.2]; omega) b hb) _ (primitivePair_left_resolved P i i)]
    exact B.geometricSector_input I.val b hb (primitivePair P i i) (h i i _ (by rw [I.property.2]; omega) b hb) false

omit [Finite ι] in

theorem pairStar_range :
    (⨆ j, (B.pairStar hlarge P h j).range) =
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  apply le_antisymm
  · apply iSup_le
    rintro j x ⟨s,rfl⟩
    exact B.pairStar_mem hlarge P h j s
  · rw [smallFamilyEval_range]
    apply iSup_le
    intro I
    apply iSup_le
    rintro j x ⟨s,rfl⟩
    obtain ⟨t,rfl⟩ := universalProjection_surjective (alternatingGroup I.val) s
    apply le_iSup (fun j => (B.pairStar hlarge P h j).range) j
    exact ⟨universalMap (subtypeAlternatingHom I.val) t,
      DFunLike.congr_fun (B.pairStar_small hlarge P h I j) t⟩

end InitialCoverSystem
end PairControl

section AssignmentExclusions
variable {E S G K ι Ω : Type*} [Group E] [Group S] [Group G] [Group K]

noncomputable def copySourceMap (π : E →* S) : FreeGroup (Option ι × E) →* FreeGroup (Option ι × S) :=
  FreeGroup.map (fun p => (p.1,π p.2))

noncomputable def formalAssignmentEval (π : E →* S) :
    FreeGroup (Option ι × E) →* ((ι → Bool) → S) :=
  (assignmentEval (fun i : ι => {σ : ι → Bool | σ i = true})).comp (copySourceMap π)

theorem formalAssignmentEval_surjective [Finite ι] [Group.IsPerfect S]
    (π : E →* S) (hπ : Function.Surjective π) : Function.Surjective (formalAssignmentEval (ι := ι) π) := by
  have hv : Function.Surjective (assignmentEval (E := S) (fun i : ι => {σ : ι → Bool | σ i = true})) := by
    apply assignmentEval_surjective
    intro σ τ h
    funext i
    exact Bool.eq_iff_iff.mpr (h i)
  have hw : Function.Surjective (copySourceMap (ι := ι) π) := by
    apply FreeGroup.map_surjective
    rintro ⟨i,s⟩
    obtain ⟨t,rfl⟩ := hπ s
    exact ⟨(i,t),rfl⟩
  exact hv.comp hw

theorem forbidden_factor_trivial [Finite ι] [Group.IsPerfect S]
    (π : E →* S) (hπ : Function.Surjective π)
    (F : Option ι → E →* G) (ρ : G →* K) (c : S →* K)
    (σ : ι → Bool) (pattern : Ω → ι → Bool)
    (hforbid : σ ∉ Set.range pattern)
    (hwhole : ρ.comp (F none) = c.comp π)
    (hcomponent : ρ.comp (copyFamilyEval F) =
      c.comp ((Pi.evalMonoidHom _ σ).comp (formalAssignmentEval π)))
    (hlocal : ∀ w, ((assignmentPullback pattern).comp (formalAssignmentEval π)) w = 1 →
      ∀ t, Commute (copyFamilyEval F w) (F none t)) : ∀ s, c s = 1 := by
  classical
  have hcomm (s t : S) : Commute (c s) (c t) := by
    obtain ⟨w,hw⟩ := formalAssignmentEval_surjective (ι := ι) π hπ (Pi.mulSingle σ s)
    have hmodel : ((assignmentPullback pattern).comp (formalAssignmentEval π)) w = 1 := by
      ext ω
      change formalAssignmentEval π w (pattern ω) = 1
      rw [hw,Pi.mulSingle_eq_of_ne]
      exact fun he => hforbid ⟨ω,he⟩
    obtain ⟨v,hv⟩ := hπ t
    have hh := (hlocal w hmodel v).map ρ
    have he := DFunLike.congr_fun hcomponent w
    have ht := DFunLike.congr_fun hwhole v
    simp only [MonoidHom.comp_apply,Pi.evalMonoidHom_apply,hw,Pi.mulSingle_eq_same] at he
    simp only [MonoidHom.comp_apply,hv] at ht
    rwa [he,ht] at hh
  let : IsMulCommutative c.range := ⟨⟨fun x y => by
    obtain ⟨s,hs⟩ := x.property
    obtain ⟨t,ht⟩ := y.property
    apply Subtype.ext
    change x.val*y.val = y.val*x.val
    rw [← hs,← ht]
    exact (hcomm s t).eq⟩⟩
  intro s
  exact congrArg Subtype.val (perfect_hom_to_commGroup c.rangeRestrict s)

theorem formal_component_of_inputs (π : E →* S)
    (F : Option ι → E →* G) (ρ : G →* K) (c : S →* K) (σ : ι → Bool)
    (hwhole : ρ.comp (F none) = c.comp π)
    (hinput : ∀ i s, ρ (F (some i) s) = if σ i then c (π s) else 1) :
    ρ.comp (copyFamilyEval F) = c.comp ((Pi.evalMonoidHom _ σ).comp (formalAssignmentEval π)) := by
  apply FreeGroup.ext_hom
  rintro ⟨i,s⟩
  cases i with
  | none => simpa only [MonoidHom.comp_apply,copyFamilyEval_of,formalAssignmentEval,copySourceMap,
      FreeGroup.map.of,assignmentEval,maskFamily,sectorMask_of_mem _ _ _ (Set.mem_univ _),
      Pi.evalMonoidHom_apply] using DFunLike.congr_fun hwhole s
  | some i =>
    simp only [MonoidHom.comp_apply,copyFamilyEval_of,formalAssignmentEval,copySourceMap,
      FreeGroup.map.of,assignmentEval,maskFamily,Pi.evalMonoidHom_apply]
    cases hs : σ i <;> simp [sectorMask,hinput,hs]

end AssignmentExclusions

end SimpleAmenable
end
end

end OAI
