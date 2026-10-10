import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.ReserveAtom

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AssignmentAtoms

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [DecidableEq Ω]

noncomputable def assignmentAtom (a : SwapLabel I) (t : Ω × SwapLabel I) :
    Ω → alternatingGroup I := Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1 (reserveAtom a t.2)

theorem supported_assignmentAtoms_generate [Finite Ω] (S : Finset I) (a : SwapLabel I)
    (ha : a.val.support ⊆ S) (g : Ω → alternatingGroup I)
    (hg : ∀ ω, (g ω).val.support ⊆ S) :
    g ∈ Subgroup.closure (Set.range (fun t : {t : Ω × SwapLabel I // t.2.val.support ⊆ S} =>
      assignmentAtom a t.val)) := by
  let K := Subgroup.closure (Set.range
    (fun t : {t : Ω × SwapLabel I // t.2.val.support ⊆ S} => assignmentAtom a t.val))
  apply Subgroup.pi_mem_of_mulSingle_mem g
  intro ω
  have hle : Subgroup.closure {h : alternatingGroup I | ∃ t : SwapLabel I,
      t.val.support ⊆ S ∧ h = reserveAtom a t} ≤
      K.comap (MonoidHom.mulSingle (fun _ : Ω => alternatingGroup I) ω) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t,ht,rfl⟩
    exact Subgroup.subset_closure ⟨⟨(ω,t),ht⟩,rfl⟩
  exact hle (supported_reserveAtoms_generate S a ha (g ω) (hg ω))

theorem assignmentAtoms_generate [Finite Ω] (a : SwapLabel I) :
    Subgroup.closure (Set.range (assignmentAtom (Ω := Ω) a)) = ⊤ := by
  apply top_unique
  intro g _
  have h := supported_assignmentAtoms_generate Finset.univ a (Finset.subset_univ _) g
    (fun _ => Finset.subset_univ _)
  have hsub : Set.range (fun t : {t : Ω × SwapLabel I // t.2.val.support ⊆ Finset.univ} =>
      assignmentAtom a t.val) ⊆ Set.range (assignmentAtom a) := by
    rintro _ ⟨t,rfl⟩
    exact ⟨t.val,rfl⟩
  exact Subgroup.closure_mono hsub h

instance assignmentSwapMulAction : MulAction (Ω → alternatingGroup I) (Ω × SwapLabel I) where
  smul g t := (t.1, swapLabelConj (g t.1).val t.2)
  one_smul t := by
    apply Prod.ext rfl
    apply Subtype.ext
    change 1 * t.2.val * 1⁻¹ = t.2.val
    simp
  mul_smul g h t := by
    apply Prod.ext rfl
    apply Subtype.ext
    change (g t.1).val * (h t.1).val * t.2.val *
      ((g t.1).val * (h t.1).val)⁻¹ =
      (g t.1).val * ((h t.1).val * t.2.val * (h t.1).val⁻¹) * (g t.1).val⁻¹
    group

omit [DecidableEq Ω] in
theorem assignmentSwap_smul_fst (g : Ω → alternatingGroup I) (t : Ω × SwapLabel I) :
    (g • t).1 = t.1 := rfl

theorem assignmentSwap_base_atom (a : SwapLabel I) (ω : Ω) :
    assignmentAtom a (ω,a) = 1 := by
  simp [assignmentAtom,reserveAtom_base]

theorem assignmentAtom_conjugation (a : SwapLabel I) (g : Ω → alternatingGroup I)
    (t : Ω × SwapLabel I) :
    g * assignmentAtom a t * g⁻¹ =
      (assignmentAtom a (g • (t.1,a)))⁻¹ * assignmentAtom a (g • t) := by
  funext ω
  by_cases hω : ω = t.1
  · subst ω
    change g t.1 * Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1 (reserveAtom a t.2) t.1 * (g t.1)⁻¹ =
      (Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1 (reserveAtom a (swapLabelConj (g t.1).val a)) t.1)⁻¹ *
        Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1 (reserveAtom a (swapLabelConj (g t.1).val t.2)) t.1
    simp only [Pi.mulSingle_eq_same]
    apply Subtype.ext
    rw [reserveAtom_difference]
    change (g t.1).val * (a.val * t.2.val) * (g t.1).val⁻¹ =
      ((g t.1).val * a.val * (g t.1).val⁻¹) *
        ((g t.1).val * t.2.val * (g t.1).val⁻¹)
    group
  · change g ω * Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1 (reserveAtom a t.2) ω * (g ω)⁻¹ =
      (Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1 (reserveAtom a (swapLabelConj (g t.1).val a)) ω)⁻¹ *
        Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1 (reserveAtom a (swapLabelConj (g t.1).val t.2)) ω
    simp [Pi.mulSingle_eq_of_ne hω]

end AssignmentAtoms

section SupportedAtomWords

variable {J K D Q : Type*} [Group D] [Group Q]

theorem hom_comp_freeLift (q : D →* Q) (u : J → D) :
    q.comp (FreeGroup.lift u) = FreeGroup.lift (fun j => q (u j)) := by
  apply FreeGroup.ext_hom
  intro j
  simp

theorem freeLift_comp_map (u : J → D) (b : K → J) :
    (FreeGroup.lift u).comp (FreeGroup.map b) = FreeGroup.lift (fun k => u (b k)) := by
  apply FreeGroup.ext_hom
  intro k
  simp

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [DecidableEq Ω] [Finite Ω]

theorem supported_atom_word (L : Finset I → Subgroup D) (hmono : Monotone L)
    (E : Finset I) (a : SwapLabel I) (ha : a.val.support ⊆ E)
    (u : Ω × SwapLabel I → D)
    (hu : ∀ t, u t ∈ L (E ∪ t.2.val.support))
    (S : Finset I) (hES : E ⊆ S) (g : Ω → alternatingGroup I)
    (hg : ∀ ω, (g ω).val.support ⊆ S) :
    ∃ w : FreeGroup (Ω × SwapLabel I),
      FreeGroup.lift (assignmentAtom a) w = g ∧ FreeGroup.lift u w ∈ L S := by
  let T := {t : Ω × SwapLabel I // t.2.val.support ⊆ S}
  have hm : g ∈ (FreeGroup.lift (fun t : T => assignmentAtom a t.val)).range := by
    rw [FreeGroup.range_lift_eq_closure]
    exact supported_assignmentAtoms_generate S a (ha.trans hES) g hg
  obtain ⟨w,hw⟩ := hm
  have hle : (FreeGroup.lift (fun t : T => u t.val)).range ≤ L S := by
    rw [FreeGroup.range_lift_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t,rfl⟩
    exact hmono (Finset.union_subset hES t.property) (hu t.val)
  refine ⟨FreeGroup.map (Subtype.val : T → Ω × SwapLabel I) w, ?_, ?_⟩
  · change ((FreeGroup.lift (assignmentAtom a)).comp (FreeGroup.map Subtype.val)) w = g
    rw [freeLift_comp_map]
    exact hw
  · change ((FreeGroup.lift u).comp (FreeGroup.map Subtype.val)) w ∈ L S
    rw [freeLift_comp_map]
    exact hle ⟨w,rfl⟩

end SupportedAtomWords

section AtomSupportBounds

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [DecidableEq Ω]

theorem swapLabel_card_support (t : SwapLabel I) : t.val.support.card = 2 :=
  Equiv.Perm.card_support_eq_two.mpr t.property

theorem swapLabelConj_support (g : Equiv.Perm I) (t : SwapLabel I) (S : Finset I)
    (hg : g.support ⊆ S) (ht : t.val.support ⊆ S) :
    (swapLabelConj g t).val.support ⊆ S := by
  change (g * t.val * g⁻¹).support ⊆ S
  apply (Equiv.Perm.support_mul_le _ _).trans
  apply Finset.union_subset
  · exact (Equiv.Perm.support_mul_le _ _).trans (Finset.union_subset hg ht)
  · simpa only [Equiv.Perm.support_inv] using hg

theorem assignmentAtom_support (a : SwapLabel I) (t : Ω × SwapLabel I) (ω : Ω) :
    ((assignmentAtom a t) ω).val.support ⊆ a.val.support ∪ t.2.val.support := by
  by_cases h : ω = t.1
  · subst ω
    change (Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1
      (reserveAtom a t.2) t.1).val.support ⊆ _
    rw [Pi.mulSingle_eq_same]
    exact Equiv.Perm.support_mul_le a.val t.2.val
  · simp only [assignmentAtom,Pi.mulSingle_eq_of_ne h,OneMemClass.coe_one,
      Equiv.Perm.support_one,Finset.empty_subset]

theorem atom_conjugation_support (E : Finset I) (a : SwapLabel I)
    (ha : a.val.support ⊆ E) (s t : Ω × SwapLabel I) :
    ((assignmentAtom a s • (t.1,a)).2).val.support ⊆
        E ∪ s.2.val.support ∪ t.2.val.support ∧
    ((assignmentAtom a s • t).2).val.support ⊆
        E ∪ s.2.val.support ∪ t.2.val.support := by
  have hgs : ((assignmentAtom a s) t.1).val.support ⊆
      E ∪ s.2.val.support ∪ t.2.val.support :=
    (assignmentAtom_support a s t.1).trans
      ((Finset.union_subset_union_left ha).trans Finset.subset_union_left)
  constructor
  · exact swapLabelConj_support _ _ _ hgs
      (ha.trans (Finset.subset_union_left.trans Finset.subset_union_left))
  · exact swapLabelConj_support _ _ _ hgs Finset.subset_union_right

variable {D : Type*} [Group D]

theorem exists_supported_atom_words (L : Finset I → Subgroup D)
    (v : D →* (Ω → alternatingGroup I)) (E : Finset I) (hE : E.card = 5)
    (a : SwapLabel I) (ha : a.val.support ⊆ E)
    (hcomplete : ∀ S : Finset I, 5 ≤ S.card → S.card ≤ 7 → ∀ g : Ω → alternatingGroup I,
      (∀ ω, (g ω).val.support ⊆ S) → ∃ d ∈ L S, v d = g) :
    ∃ u : Ω × SwapLabel I → D, ∀ t,
      u t ∈ L (E ∪ t.2.val.support) ∧ v (u t) = assignmentAtom a t := by
  classical
  have h (t : Ω × SwapLabel I) : ∃ d ∈ L (E ∪ t.2.val.support),
      v d = assignmentAtom a t := by
    apply hcomplete (E ∪ t.2.val.support)
    · rw [← hE]
      exact Finset.card_le_card Finset.subset_union_left
    · exact (Finset.card_union_le _ _).trans (by rw [hE,swapLabel_card_support])
    · intro ω
      exact (assignmentAtom_support a t ω).trans (Finset.union_subset_union_left ha)
  choose u hu hv using h
  exact ⟨u,fun t => ⟨hu t,hv t⟩⟩

end AtomSupportBounds

end SimpleAmenable
end
end

end OAI
