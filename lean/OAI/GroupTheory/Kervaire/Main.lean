import OAI.GroupTheory.Kervaire.WordNormalization

namespace OAI

section
noncomputable section

namespace KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {I : Type} {A : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Group A]

lemma relator_ribbon_realized (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i=1 ∨ s i = -1) (i : I) (l : List I)
    (hc : Circle ρ i l) (hn : (i::l).Nodup) (hcover : ∀ j, j ∈ i::l) :
    Realized ρ a s (dartEval s a (i::l)) :=
  ⟨(I⊕I)⊕PUnit,PUnit,inferInstance,inferInstance,inferInstance,Sum.inr PUnit.unit,
    (i::l).map (fun j ↦ Sum.inl (Sum.inr j)),OuterRibbon.base ρ hρ a s hs i l hc hn hcover,
    OuterRibbon.value_base ρ hρ a s hs i l hc hn hcover⟩

lemma relator_normalClosure_coefficient_eq_one (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j)
    (a : I → A) (s : I → ℤ) (hs : ∀ i, s i=1 ∨ s i = -1)
    (hsum : (∑ i, s i)=1 ∨ (∑ i, s i) = -1) (i : I) (l : List I)
    (hc : Circle ρ i l) (hn : (i::l).Nodup) (hcover : ∀ j, j ∈ i::l)
    (g : A) (hg : Coprod.inl g ∈ Subgroup.normalClosure ({dartEval s a (i::l)} : Set (FreeProd A))) :
    g=1 := by
  have hle : Subgroup.normalClosure ({dartEval s a (i::l)} : Set (FreeProd A)) ≤ realizedSubgroup ρ a s := by
    apply Subgroup.normalClosure_le_normal
    intro w hw
    have he : w = dartEval s a (i::l) := Set.mem_singleton_iff.mp hw
    subst w
    exact relator_ribbon_realized ρ hρ a s hs i l hc hn hcover
  exact (hle hg).coefficient_eq_one hρ hs hsum
end KervaireRibbon

namespace Kervaire
open Monoid Multiplicative Equiv
open KervaireRibbon
open scoped Classical

/-- The finite relator indices range over positions, not over the possibly
uncountable coefficient group. The original element and exponent are preserved. -/
lemma normalClosure_coefficient_eq_one {A : Type*} [Group A] (w : WordGroup A)
    (hw : Unimodular w) (g : A) (hg : Coprod.inl g ∈ relatorClosure w) : g=1 := by
  obtain ⟨l,hlen,hunit,heval⟩ := unit_syllables_every w
  let I := Fin l.length
  let s : I → ℤ := fun i ↦ (l.get i).1
  let a : I → A := fun i ↦ (l.get i).2
  let e : List I := List.finRange l.length
  have hne : e ≠ [] := by
    intro he
    have hpos : 0 < l.length := by omega
    have hm : (⟨0,hpos⟩ : I) ∈ e := List.mem_finRange _
    rw [he] at hm
    exact List.not_mem_nil hm
  obtain ⟨i,is,he⟩ := List.exists_cons_of_ne_nil hne
  have : Nonempty I := ⟨i⟩
  let ρ : Perm I := e.formPerm
  have hn : (i::is).Nodup := by rw [← he]; exact List.nodup_finRange _
  have hcover : ∀ j : I, j ∈ i::is := by intro j; rw [← he]; exact List.mem_finRange j
  have hc : Circle ρ i is := by change Circle e.formPerm i is; rw [he]; exact circle_formPerm i is hn
  have hρ : ∀ j k : I, ρ.SameCycle j k := by
    change ∀ j k, e.formPerm.SameCycle j k
    rw [he]
    exact formPerm_sameCycle_all i is hn hcover
  have hs : ∀ j : I, s j=1 ∨ s j = -1 := fun j ↦ hunit _ (List.get_mem l j)
  have heval' : dartEval s a (i::is) = w := by
    rw [← he]
    change (List.map (fun j : I ↦ Coprod.inr (ofAdd (l.get j).1)*Coprod.inl (l.get j).2) e).prod = w
    change (List.map ((fun x : ℤ×A ↦ Coprod.inr (ofAdd x.1)*Coprod.inl x.2) ∘ l.get) e).prod = w
    rw [← List.map_map (f := l.get) (g := fun x : ℤ×A ↦ Coprod.inr (ofAdd x.1)*Coprod.inl x.2)]
    rw [← List.ofFn_eq_map,List.ofFn_get]
    exact heval
  have hsumEq : (∑ i : I, s i) = exponentSum w := by
    rw [← List.sum_ofFn]
    change (List.ofFn (Prod.fst ∘ l.get)).sum = _
    rw [← List.map_ofFn,List.ofFn_get]
    exact (syllableEval_exponent l).symm.trans (congrArg (fun z : FreeProd A ↦ toAdd (Coprod.snd z)) heval)
  have hsum : (∑ i : I, s i)=1 ∨ (∑ i : I, s i) = -1 := by rw [hsumEq]; exact hw
  apply relator_normalClosure_coefficient_eq_one ρ hρ a s hs hsum i is hc hn hcover g
  rw [heval']
  exact hg

universe u

theorem coefficient_injective (A : Type u) [Group A] (w : WordGroup A)
    (hw : Unimodular w) : Function.Injective (coefficientMap w) :=
  (coefficient_injective_iff w).mpr (normalClosure_coefficient_eq_one w hw)

theorem quotient_nontrivial (A : Type u) [Group A] [Nontrivial A] (w : WordGroup A) :
    Nontrivial (RelatorQuotient w) := by
  by_cases hw : Unimodular w
  · exact Function.Injective.nontrivial (coefficient_injective A w hw)
  · exact quotient_nontrivial_of_not_unimodular w hw
end Kervaire

end
end

end OAI
