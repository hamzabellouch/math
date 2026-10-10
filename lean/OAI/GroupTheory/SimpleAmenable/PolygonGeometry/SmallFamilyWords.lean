import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SmallSectorGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SmallFamilyWords

variable {α ι Ω H : Type*} [Fintype α] [DecidableEq α] [Group H]

abbrev FiveAlphabet (α : Type*) [Fintype α] [DecidableEq α] :=
  FiveSubalphabet (Finset.univ : Finset α)

abbrev SmallFamilyLabel (α ι : Type*) [Fintype α] [DecidableEq α] :=
  Σ I : FiveAlphabet α, Option ι × alternatingGroup I.val

abbrev SmallFamilyWord (α ι : Type*) [Fintype α] [DecidableEq α] :=
  FreeGroup (SmallFamilyLabel α ι)

noncomputable def smallFamilyEval
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H) :
    SmallFamilyWord α ι →* H := FreeGroup.lift (fun l => F l.1 l.2.1 l.2.2)

@[simp] theorem smallFamilyEval_of
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (I : FiveAlphabet α) (i : Option ι) (s : alternatingGroup I.val) :
    smallFamilyEval F (FreeGroup.of ⟨I,i,s⟩) = F I i s := FreeGroup.lift_apply_of

theorem smallFamilyEval_range
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H) :
    (smallFamilyEval F).range = ⨆ I, ⨆ i, (F I i).range := by
  rw [smallFamilyEval,FreeGroup.range_lift_eq_closure]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨I,i,s⟩,rfl⟩
    exact (le_iSup (fun I => ⨆ i, (F I i).range) I)
      ((le_iSup (fun i => (F I i).range) i) ⟨s,rfl⟩)
  · apply iSup_le
    intro I
    apply iSup_le
    rintro i x ⟨s,rfl⟩
    exact Subgroup.subset_closure ⟨⟨I,i,s⟩,rfl⟩

theorem smallFamilyEval_perfect
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H) :
    Group.IsPerfect (smallFamilyEval F).range := by
  rw [smallFamilyEval_range]
  let (I : FiveAlphabet α) (i : Option ι) : Group.IsPerfect (F I i).range :=
    Group.IsPerfect.range (F I i)
  let (I : FiveAlphabet α) : Group.IsPerfect ↥(⨆ i, (F I i).range) :=
    perfect_iSup (fun i => (F I i).range)
  exact perfect_iSup (fun I => ⨆ i, (F I i).range)

noncomputable def smallFamilyLocal (S : Finset α) : Subgroup (SmallFamilyWord α ι) :=
  Subgroup.closure {w | ∃ l : SmallFamilyLabel α ι, l.1.val ⊆ S ∧ w = FreeGroup.of l}

theorem smallFamilyLocal_mono : Monotone (smallFamilyLocal (α := α) (ι := ι)) := by
  intro S T hST
  apply Subgroup.closure_mono
  rintro w ⟨l,hl,rfl⟩
  exact ⟨l,hl.trans hST,rfl⟩

theorem smallFamilyLocal_of (l : SmallFamilyLabel α ι) {S : Finset α} (h : l.1.val ⊆ S) :
    FreeGroup.of l ∈ smallFamilyLocal (ι := ι) S :=
  Subgroup.subset_closure ⟨l,h,rfl⟩

theorem smallFamilyLocal_generate :
    Subgroup.closure {w : SmallFamilyWord α ι | ∃ S : Finset α,
      S.card ≤ 5 ∧ w ∈ smallFamilyLocal S} = ⊤ := by
  apply top_unique
  rw [← FreeGroup.closure_range_of]
  apply Subgroup.closure_mono
  rintro w ⟨l,rfl⟩
  exact ⟨l.1.val,by rw [l.1.property.2],smallFamilyLocal_of l (Finset.Subset.refl _)⟩

noncomputable def alphabetAssignment (I : Finset α) :
    (Ω → alternatingGroup I) →* (Ω → alternatingGroup α) where
  toFun g ω := subtypeAlternatingHom I (g ω)
  map_one' := by funext ω; exact map_one _
  map_mul' g h := by funext ω; exact map_mul _ _ _

theorem alphabetAssignment_support (I : Finset α) (g : Ω → alternatingGroup I) (ω : Ω) :
    ((alphabetAssignment I g) ω).val.support ⊆ I :=
  (subtypeAlternatingHom_mem_range I _).mp ⟨g ω,rfl⟩

theorem alphabetAssignment_range (I : Finset α) (g : Ω → alternatingGroup α) :
    g ∈ (alphabetAssignment (Ω := Ω) I).range ↔ ∀ ω, (g ω).val.support ⊆ I := by
  constructor
  · rintro ⟨g,rfl⟩
    exact alphabetAssignment_support I g
  · intro h
    choose f hf using fun ω => (subtypeAlternatingHom_mem_range I (g ω)).mpr (h ω)
    exact ⟨f,funext hf⟩

theorem alphabetAssignment_mask (I : Finset α) (U : ι → Set Ω) (i : Option ι) :
    (alphabetAssignment I).comp (maskFamily U i) =
      (maskFamily U i).comp (subtypeAlternatingHom I) := by
  classical
  ext s ω
  cases i with
  | none => simp [alphabetAssignment,maskFamily,sectorMask]
  | some i => by_cases h : ω ∈ U i <;> simp [alphabetAssignment,maskFamily,sectorMask,h]

noncomputable def smallFamilyModel (U : ι → Set Ω) :
    SmallFamilyWord α ι →* (Ω → alternatingGroup α) :=
  smallFamilyEval (fun I i => (maskFamily U i).comp (subtypeAlternatingHom I.val))

theorem smallFamilyModel_support (U : ι → Set Ω) (S : Finset α)
    (w : SmallFamilyWord α ι) (hw : w ∈ smallFamilyLocal S) :
    ∀ ω, ((smallFamilyModel U w) ω).val.support ⊆ S := by
  apply (alphabetAssignment_range S _).mp
  have hh : smallFamilyLocal (ι := ι) S ≤
      ((alphabetAssignment (Ω := Ω) S).range).comap (smallFamilyModel U) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨l,hl,rfl⟩
    apply (alphabetAssignment_range S _).mpr
    intro ω
    classical
    have hs := (subtypeAlternatingHom_mem_range l.1.val _).mp ⟨l.2.2,rfl⟩
    change ((maskFamily U l.2.1 (subtypeAlternatingHom l.1.val l.2.2)) ω).val.support ⊆ S
    cases l.2.1 with
    | none => simpa [maskFamily,sectorMask] using hs.trans hl
    | some i =>
      by_cases h : ω ∈ U i
      · simpa [maskFamily,sectorMask,h] using hs.trans hl
      · simp [maskFamily,sectorMask,h]
  exact hh hw

end SmallFamilyWords

section SmallFamilyComplete
variable {α ι Ω H : Type*} [Fintype α] [DecidableEq α] [Group H]

theorem smallFamilyModel_mask_mem (U : ι → Set Ω) (S : Finset α) (hS : 5 ≤ S.card)
    (i : Option ι) (s : alternatingGroup S) :
    maskFamily U i (subtypeAlternatingHom S s) ∈
      (smallFamilyLocal S).map (smallFamilyModel U) := by
  let K := ((smallFamilyLocal S).map (smallFamilyModel U)).comap
    ((maskFamily U i).comp (subtypeAlternatingHom S))
  have hK : K = ⊤ := by
    apply top_unique
    rw [← subalphabet_five_generate S hS]
    apply iSup_le
    intro I x hx
    obtain ⟨t,rfl⟩ := hx
    let I' : FiveAlphabet α := ⟨I.val,Finset.subset_univ _,I.property.2⟩
    refine ⟨FreeGroup.of ⟨I',i,t⟩,smallFamilyLocal_of _ I.property.1,?_⟩
    change maskFamily U i (subtypeAlternatingHom I.val t) =
      maskFamily U i (subtypeAlternatingHom S (subalphabetHom I.property.1 t))
    exact congrArg (maskFamily U i)
      (DFunLike.congr_fun (subtypeAlternatingHom_comp I.property.1) t).symm
  exact (show s ∈ K from hK ▸ Subgroup.mem_top s)

theorem smallFamilyModel_complete [Finite ι] [Finite Ω]
    (U : ι → Set Ω) (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω = ν)
    (S : Finset α) (hS : 5 ≤ S.card) (g : Ω → alternatingGroup α)
    (hg : ∀ ω, (g ω).val.support ⊆ S) :
    ∃ w ∈ smallFamilyLocal S, smallFamilyModel U w = g := by
  let : Group.IsPerfect (alternatingGroup S) := alphabetPerfect S hS
  obtain ⟨t,ht⟩ := (alphabetAssignment_range S g).mpr hg
  let K := ((smallFamilyLocal S).map (smallFamilyModel U)).comap (alphabetAssignment S)
  have hm (i : Option ι) (s : alternatingGroup S) : maskFamily U i s ∈ K := by
    change alphabetAssignment S (maskFamily U i s) ∈
      (smallFamilyLocal S).map (smallFamilyModel U)
    rw [← MonoidHom.comp_apply,alphabetAssignment_mask]
    exact smallFamilyModel_mask_mem U S hS i s
  have hK : K = ⊤ := assignment_group_generated U hsep K (hm none) (fun i => hm (some i))
  have htK : t ∈ K := hK ▸ Subgroup.mem_top t
  change alphabetAssignment S t ∈ (smallFamilyLocal S).map (smallFamilyModel U) at htK
  rwa [ht] at htK

theorem smallFamilyLocal_map_le
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (S : Finset α) (K : Subgroup H)
    (h : ∀ I, I.val ⊆ S → ∀ i, (F I i).range ≤ K) :
    (smallFamilyLocal S).map (smallFamilyEval F) ≤ K := by
  apply (Subgroup.map_le_iff_le_comap).mpr
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨l,hl,rfl⟩
  exact h l.1 hl l.2.1 ⟨l.2.2,(FreeGroup.lift_apply_of).symm⟩

end SmallFamilyComplete

end SimpleAmenable
end
end

end OAI
