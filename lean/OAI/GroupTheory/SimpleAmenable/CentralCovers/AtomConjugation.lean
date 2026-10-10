import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConjugationTransport

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AtomConjugation
variable {J M H T : Type*} [Group M] [Group H] [MulAction M T]

theorem difference_conjugation_of_atom (p : J → M) (f : J → H) (Y : T → H)
    (b : T → T) (R : T → T → Prop) (hb : ∀ t u, R t u → b t = b u)
    (hconj : ∀ j t, f j * Y t * (f j)⁻¹ =
      (Y (p j • b t))⁻¹ * Y (p j • t)) :
    ∀ j t u, R t u →
      f j * (Y t)⁻¹ * Y u * (f j)⁻¹ =
        (Y (p j • t))⁻¹ * Y (p j • u) := by
  intro j t u htu
  calc
    f j * (Y t)⁻¹ * Y u * (f j)⁻¹ =
        (f j * Y t * (f j)⁻¹)⁻¹ * (f j * Y u * (f j)⁻¹) := by group
    _ = ((Y (p j • b t))⁻¹ * Y (p j • t))⁻¹ *
        ((Y (p j • b u))⁻¹ * Y (p j • u)) := by rw [hconj, hconj]
    _ = _ := by rw [hb t u htu]; group

theorem centralLaw_of_atom_conjugations (p : J → M) (f : J → H) (Y : T → H)
    (b : T → T) (R : T → T → Prop) (hb : ∀ t u, R t u → b t = b u)
    (hRb : ∀ t, R (b t) t) (hYb : ∀ t, Y (b t) = 1)
    (hR : ∀ (g : M) t u, R t u → R (g • t) (g • u))
    (hconj : ∀ j t, f j * Y t * (f j)⁻¹ =
      (Y (p j • b t))⁻¹ * Y (p j • t))
    (hgen : Subgroup.closure (Set.range Y) = ⊤) :
    HasCentralLaw (FreeGroup.lift p) (FreeGroup.lift f) := by
  apply centralLaw_of_difference_conjugations p f Y R hR
    (difference_conjugation_of_atom p f Y b R hb hconj)
  apply top_unique
  rw [← hgen]
  apply Subgroup.closure_mono
  rintro _ ⟨t,rfl⟩
  exact ⟨b t,t,hRb t,by rw [hYb]; simp⟩

end AtomConjugation

section LocalSupportLaws

variable {I D M H : Type*} [DecidableEq I] [Group D] [Group M] [Group H]

def LocalCentralLaw (L : Finset I → Subgroup D) (v : D →* M) (f : D →* H)
    (S : Finset I) : Prop :=
  ∀ d ∈ L S, v d = 1 → ∀ e ∈ L S, Commute (f d) (f e)

theorem local_null_is_central (L : Finset I → Subgroup D) (hmono : Monotone L)
    (v : D →* M) (f : D →* H)
    (hgen : Subgroup.closure {h : H | ∃ T : Finset I, T.card ≤ 5 ∧
      ∃ e ∈ L T, h = f e} = ⊤)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    {S : Finset I} (hS : S.card ≤ 10) {d : D} (hd : d ∈ L S) (hv : v d = 1) :
    f d ∈ Subgroup.center H := by
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← hgen,
    Subgroup.centralizer_closure]
  apply Subgroup.mem_centralizer_iff.mpr
  rintro z ⟨T,hT,e,he,rfl⟩
  have hc : (S ∪ T).card ≤ 15 := (Finset.card_union_le S T).trans (by omega)
  exact (hlaw (S ∪ T) hc d (hmono Finset.subset_union_left hd) hv e
    (hmono Finset.subset_union_right he)).symm.eq

theorem local_equality_mod_center (L : Finset I → Subgroup D) (hmono : Monotone L)
    (v : D →* M) (f : D →* H)
    (hgen : Subgroup.closure {h : H | ∃ T : Finset I, T.card ≤ 5 ∧
      ∃ e ∈ L T, h = f e} = ⊤)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    {S : Finset I} (hS : S.card ≤ 10) {d e : D}
    (hd : d ∈ L S) (he : e ∈ L S) (hv : v d = v e) :
    QuotientGroup.mk' (Subgroup.center H) (f d) =
      QuotientGroup.mk' (Subgroup.center H) (f e) := by
  have hz := local_null_is_central L hmono v f hgen hlaw hS
    ((L S).mul_mem hd ((L S).inv_mem he)) (by simp [hv] : v (d * e⁻¹) = 1)
  have hh : f (d * e⁻¹) ∈ (QuotientGroup.mk' (Subgroup.center H)).ker := by
    rwa [QuotientGroup.ker_mk']
  have hh' : QuotientGroup.mk' (Subgroup.center H) (f (d * e⁻¹)) = 1 := hh
  simpa only [map_mul, map_inv, mul_inv_eq_one] using hh'

end LocalSupportLaws

section ReserveAtoms

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev SwapLabel (I : Type*) [DecidableEq I] :=
  {t : Equiv.Perm I // t.IsSwap}

noncomputable def reserveAtom (a t : SwapLabel I) : alternatingGroup I :=
  ⟨a.val * t.val, Equiv.Perm.mul_mem_alternatingGroup_of_isSwap a.property t.property⟩

omit [Fintype I] in
theorem swapLabel_inv (t : SwapLabel I) : t.val⁻¹ = t.val := by
  obtain ⟨i,j,_,h⟩ := t.property
  simp [h]

theorem reserveAtom_base (a : SwapLabel I) : reserveAtom a a = 1 := by
  apply Subtype.ext
  change a.val * a.val = 1
  nth_rw 1 [← swapLabel_inv a]
  exact inv_mul_cancel a.val

theorem reserveAtom_difference (a s t : SwapLabel I) :
    ((reserveAtom a s)⁻¹ * reserveAtom a t : alternatingGroup I).val = s.val * t.val := by
  change (a.val * s.val)⁻¹ * (a.val * t.val) = _
  calc
    _ = s.val⁻¹ * t.val := by group
    _ = _ := by rw [swapLabel_inv]

theorem reserveAtoms_generate (a : SwapLabel I) :
    Subgroup.closure (Set.range (reserveAtom a)) = ⊤ := by
  apply top_unique
  rw [← alternatingGroup.closure_isThreeCycles_eq_top]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < g.val.support.card by rw [hg.card_support]; omega)
  have hne : i ≠ g.val i := (Equiv.Perm.mem_support.mp hi).symm
  let s : SwapLabel I := ⟨Equiv.swap i (g.val i), i, g.val i, hne, rfl⟩
  let t : SwapLabel I := ⟨Equiv.swap (g.val i) (g.val (g.val i)),
    g.val i, g.val (g.val i), fun h => hne (g.val.injective h), rfl⟩
  have heq : g = (reserveAtom a s)⁻¹ * reserveAtom a t := by
    apply Subtype.ext
    rw [reserveAtom_difference]
    exact hg.eq_swap_mul_swap_iff_mem_support.mpr hi
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨s,rfl⟩))
    (Subgroup.subset_closure ⟨t,rfl⟩)

def swapLabelConj (g : Equiv.Perm I) (t : SwapLabel I) : SwapLabel I := by
  refine ⟨g * t.val * g⁻¹, ?_⟩
  obtain ⟨i,j,hij,ht⟩ := t.property
  refine ⟨g i,g j,fun h => hij (g.injective h), ?_⟩
  rw [ht]
  rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right]

theorem reserveAtom_conjugation (a s t : SwapLabel I) :
    reserveAtom a s * reserveAtom a t * (reserveAtom a s)⁻¹ =
      (reserveAtom a (swapLabelConj (reserveAtom a s).val a))⁻¹ *
       reserveAtom a (swapLabelConj (reserveAtom a s).val t) := by
  apply Subtype.ext
  rw [reserveAtom_difference]
  change (a.val*s.val) * (a.val*t.val) * (a.val*s.val)⁻¹ =
    ((a.val*s.val) * a.val * (a.val*s.val)⁻¹) *
    ((a.val*s.val) * t.val * (a.val*s.val)⁻¹)
  group

end ReserveAtoms

end SimpleAmenable
end
end

end OAI
