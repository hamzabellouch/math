import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.AssignmentAtoms

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section LocalAtomComparison

variable {I Ω D H : Type*} [Fintype I] [DecidableEq I] [DecidableEq Ω] [Finite Ω]
    [Group D] [Group H]

theorem local_atom_comparison (L : Finset I → Subgroup D) (hmono : Monotone L)
    (v : D →* (Ω → alternatingGroup I)) (f : D →* H)
    (hgen : Subgroup.closure {h : H | ∃ T : Finset I, T.card ≤ 5 ∧
      ∃ e ∈ L T, h = f e} = ⊤)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    (E : Finset I) (hE : E.card = 5) (a : SwapLabel I) (ha : a.val.support ⊆ E)
    (u : Ω × SwapLabel I → D)
    (hu : ∀ t, u t ∈ L (E ∪ t.2.val.support))
    (huv : ∀ t, v (u t) = assignmentAtom a t)
    (S : Finset I) (hS : S.card ≤ 5) (d : D) (hd : d ∈ L S)
    (hvd : ∀ ω, ((v d) ω).val.support ⊆ S) :
    ∃ w : FreeGroup (Ω × SwapLabel I),
      FreeGroup.lift (assignmentAtom a) w = v d ∧
      QuotientGroup.mk' (Subgroup.center H) (f (FreeGroup.lift u w)) =
        QuotientGroup.mk' (Subgroup.center H) (f d) := by
  obtain ⟨w,hw,hwu⟩ := supported_atom_word L hmono E a ha u hu (E ∪ S)
    Finset.subset_union_left (v d) (fun ω => (hvd ω).trans Finset.subset_union_right)
  refine ⟨w,hw,?_⟩
  have hvw : v (FreeGroup.lift u w) = v d := by
    change (v.comp (FreeGroup.lift u)) w = v d
    rw [hom_comp_freeLift]
    simpa only [huv] using hw
  have hc : (E ∪ S).card ≤ 10 :=
    (Finset.card_union_le _ _).trans (by omega)
  exact local_equality_mod_center L hmono v f hgen hlaw hc hwu
    (hmono Finset.subset_union_right hd) hvw

theorem local_atoms_generate_center_quotient (L : Finset I → Subgroup D)
    (hmono : Monotone L) (v : D →* (Ω → alternatingGroup I)) (f : D →* H)
    (hgen : Subgroup.closure {h : H | ∃ T : Finset I, T.card ≤ 5 ∧
      ∃ e ∈ L T, h = f e} = ⊤)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    (hsupp : ∀ S : Finset I, ∀ d ∈ L S, ∀ ω, ((v d) ω).val.support ⊆ S)
    (E : Finset I) (hE : E.card = 5) (a : SwapLabel I) (ha : a.val.support ⊆ E)
    (u : Ω × SwapLabel I → D)
    (hu : ∀ t, u t ∈ L (E ∪ t.2.val.support))
    (huv : ∀ t, v (u t) = assignmentAtom a t) :
    Subgroup.closure (Set.range (fun t => QuotientGroup.mk' (Subgroup.center H) (f (u t)))) = ⊤ := by
  let q := QuotientGroup.mk' (Subgroup.center H)
  let Y := fun t => q (f (u t))
  rw [← FreeGroup.range_lift_eq_closure]
  apply top_unique
  have hle : (⊤ : Subgroup H) ≤ (FreeGroup.lift Y).range.comap q := by
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨S,hS,d,hd,rfl⟩
    obtain ⟨w,_,hw⟩ := local_atom_comparison L hmono v f hgen hlaw E hE a ha u hu huv
      S hS d hd (hsupp S d hd)
    refine ⟨w,?_⟩
    have heq := DFunLike.congr_fun (hom_comp_freeLift (q.comp f) u) w
    exact heq.symm.trans hw
  intro z _
  obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) z
  exact hle (Subgroup.mem_top h)

end LocalAtomComparison

section LocalAtomConjugation

variable {I Ω D H : Type*} [Fintype I] [DecidableEq I] [DecidableEq Ω]
    [Group D] [Group H]

theorem local_atom_conjugation (L : Finset I → Subgroup D) (hmono : Monotone L)
    (v : D →* (Ω → alternatingGroup I)) (f : D →* H)
    (hgen : Subgroup.closure {h : H | ∃ T : Finset I, T.card ≤ 5 ∧
      ∃ e ∈ L T, h = f e} = ⊤)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    (E : Finset I) (hE : E.card = 5) (a : SwapLabel I) (ha : a.val.support ⊆ E)
    (u : Ω × SwapLabel I → D)
    (hu : ∀ t, u t ∈ L (E ∪ t.2.val.support))
    (huv : ∀ t, v (u t) = assignmentAtom a t) (s t : Ω × SwapLabel I) :
    let Y := fun t => QuotientGroup.mk' (Subgroup.center H) (f (u t))
    Y s * Y t * (Y s)⁻¹ =
      (Y (assignmentAtom a s • (t.1,a)))⁻¹ * Y (assignmentAtom a s • t) := by
  dsimp only
  let S := E ∪ s.2.val.support ∪ t.2.val.support
  have hES : E ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hs : u s ∈ L S := hmono Finset.subset_union_left (hu s)
  have ht : u t ∈ L S := hmono
    (Finset.union_subset hES Finset.subset_union_right) (hu t)
  have hc := atom_conjugation_support E a ha s t
  have hb : u (assignmentAtom a s • (t.1,a)) ∈ L S :=
    hmono (Finset.union_subset hES hc.1) (hu _)
  have hd : u (assignmentAtom a s • t) ∈ L S :=
    hmono (Finset.union_subset hES hc.2) (hu _)
  have hcard : S.card ≤ 10 := by
    have h1 := Finset.card_union_le E s.2.val.support
    have h2 := Finset.card_union_le (E ∪ s.2.val.support) t.2.val.support
    rw [swapLabel_card_support] at h1 h2
    dsimp [S]
    omega
  have heq : v (u s * u t * (u s)⁻¹) =
      v ((u (assignmentAtom a s • (t.1,a)))⁻¹ * u (assignmentAtom a s • t)) := by
    simp only [map_mul,map_inv,huv]
    exact assignmentAtom_conjugation a (assignmentAtom a s) t
  have h := local_equality_mod_center L hmono v f hgen hlaw hcard
    ((L S).mul_mem ((L S).mul_mem hs ht) ((L S).inv_mem hs))
    ((L S).mul_mem ((L S).inv_mem hb) hd) heq
  simpa only [map_mul,map_inv] using h

theorem local_atom_base (L : Finset I → Subgroup D) (hmono : Monotone L)
    (v : D →* (Ω → alternatingGroup I)) (f : D →* H)
    (hgen : Subgroup.closure {h : H | ∃ T : Finset I, T.card ≤ 5 ∧
      ∃ e ∈ L T, h = f e} = ⊤)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    (E : Finset I) (hE : E.card = 5) (a : SwapLabel I)
    (u : Ω × SwapLabel I → D)
    (hu : ∀ t, u t ∈ L (E ∪ t.2.val.support))
    (huv : ∀ t, v (u t) = assignmentAtom a t) (ω : Ω) :
    QuotientGroup.mk' (Subgroup.center H) (f (u (ω,a))) = 1 := by
  have hc : (E ∪ a.val.support).card ≤ 10 :=
    (Finset.card_union_le _ _).trans (by rw [hE,swapLabel_card_support]; omega)
  have heq : v (u (ω,a)) = v 1 := by rw [huv,assignmentSwap_base_atom,map_one]
  simpa only [map_one] using local_equality_mod_center L hmono v f hgen hlaw hc
    (hu (ω,a)) (L (E ∪ a.val.support)).one_mem heq

end LocalAtomConjugation

section SmallSupportAssignment

variable {I Ω D H : Type*} [Fintype I] [DecidableEq I] [DecidableEq Ω] [Finite Ω]
    [Group D] [Group H] [Group.IsPerfect H]

theorem small_support_assignment_law_with_atoms
    (L : Finset I → Subgroup D) (hmono : Monotone L)
    (v : D →* (Ω → alternatingGroup I)) (f : D →* H) (hf : Function.Surjective f)
    (hDgen : Subgroup.closure {d : D | ∃ S : Finset I, S.card ≤ 5 ∧ d ∈ L S} = ⊤)
    (hsupp : ∀ S : Finset I, ∀ d ∈ L S, ∀ ω, ((v d) ω).val.support ⊆ S)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    (E : Finset I) (hE : E.card = 5) (a : SwapLabel I) (ha : a.val.support ⊆ E)
    (u : Ω × SwapLabel I → D)
    (hu : ∀ t, u t ∈ L (E ∪ t.2.val.support))
    (huv : ∀ t, v (u t) = assignmentAtom a t) : HasCentralLaw v f := by
  classical
  have hgen : Subgroup.closure {h : H | ∃ T : Finset I, T.card ≤ 5 ∧
      ∃ e ∈ L T, h = f e} = ⊤ := by
    have hi : f '' {d : D | ∃ S : Finset I, S.card ≤ 5 ∧ d ∈ L S} =
        {h : H | ∃ T : Finset I, T.card ≤ 5 ∧ ∃ e ∈ L T, h = f e} := by
      ext h
      constructor
      · rintro ⟨d,⟨S,hS,hd⟩,rfl⟩
        exact ⟨S,hS,d,hd,rfl⟩
      · rintro ⟨S,hS,d,hd,rfl⟩
        exact ⟨d,⟨S,hS,hd⟩,rfl⟩
    rw [← hi, ← MonoidHom.map_closure, hDgen, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hf]
  let Q := H ⧸ Subgroup.center H
  let q : H →* Q := QuotientGroup.mk' (Subgroup.center H)
  let P := FreeGroup.lift (assignmentAtom (Ω := Ω) a)
  let Y := fun t => q (f (u t))
  have hgenY : Subgroup.closure (Set.range Y) = ⊤ :=
    local_atoms_generate_center_quotient L hmono v f hgen hlaw hsupp E hE a ha u hu huv
  have hcentral : HasCentralLaw P (FreeGroup.lift Y) := by
    apply centralLaw_of_atom_conjugations (assignmentAtom a) Y Y (fun t => (t.1,a))
      (fun t s => t.1 = s.1)
    · intro t s hts
      exact Prod.ext hts rfl
    · intro t
      rfl
    · intro t
      exact local_atom_base L hmono v f hgen hlaw E hE a u hu huv t.1
    · intro g t s hts
      exact hts
    · intro s t
      exact local_atom_conjugation L hmono v f hgen hlaw E hE a ha u hu huv s t
    · exact hgenY
  have hker : P.ker ≤ (FreeGroup.lift Y).ker := by
    intro w hw
    have hz := (hasCentralLaw_iff P (FreeGroup.lift Y)).mp hcentral w hw
    change FreeGroup.lift Y w ∈ Subgroup.center (H ⧸ Subgroup.center H) at hz
    rw [perfect_center_quotient] at hz
    exact hz
  have hP : Function.Surjective P :=
    FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr (assignmentAtoms_generate a)
  let φ : (Ω → alternatingGroup I) →* Q := P.liftOfSurjective hP ⟨_,hker⟩
  have hφ : φ.comp P = FreeGroup.lift Y := P.liftOfRightInverse_comp _ _ _
  have hmap : φ.comp v = q.comp f := by
    apply MonoidHom.eq_of_eqOn_dense hDgen
    rintro d ⟨S,hS,hd⟩
    obtain ⟨w,hw,hq⟩ := local_atom_comparison L hmono v f hgen hlaw E hE a ha u hu huv
      S hS d hd (hsupp S d hd)
    change φ (v d) = q (f d)
    have hwp : P w = v d := hw
    calc
      φ (v d) = φ (P w) := congrArg φ hwp.symm
      _ = FreeGroup.lift Y w := DFunLike.congr_fun hφ w
      _ = q (f (FreeGroup.lift u w)) :=
        (DFunLike.congr_fun (hom_comp_freeLift (q.comp f) u) w).symm
      _ = q (f d) := hq
  rw [hasCentralLaw_iff]
  intro d hd
  have he := DFunLike.congr_fun hmap d
  change φ (v d) = q (f d) at he
  rw [hd,map_one] at he
  have hk : f d ∈ (QuotientGroup.mk' (Subgroup.center H)).ker := he.symm
  rwa [QuotientGroup.ker_mk'] at hk

theorem small_support_assignment_law
    (L : Finset I → Subgroup D) (hmono : Monotone L)
    (v : D →* (Ω → alternatingGroup I)) (f : D →* H) (hf : Function.Surjective f)
    (hDgen : Subgroup.closure {d : D | ∃ S : Finset I, S.card ≤ 5 ∧ d ∈ L S} = ⊤)
    (hsupp : ∀ S : Finset I, ∀ d ∈ L S, ∀ ω, ((v d) ω).val.support ⊆ S)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    (E : Finset I) (hE : E.card = 5) (a : SwapLabel I) (ha : a.val.support ⊆ E)
    (hcomplete : ∀ S : Finset I, 5 ≤ S.card → S.card ≤ 7 → ∀ g : Ω → alternatingGroup I,
      (∀ ω, (g ω).val.support ⊆ S) → ∃ d ∈ L S, v d = g) : HasCentralLaw v f := by
  obtain ⟨u,hu⟩ := exists_supported_atom_words L v E hE a ha hcomplete
  exact small_support_assignment_law_with_atoms L hmono v f hf hDgen hsupp hlaw E hE a ha u
    (fun t => (hu t).1) (fun t => (hu t).2)

end SmallSupportAssignment

end SimpleAmenable
end
end

end OAI
