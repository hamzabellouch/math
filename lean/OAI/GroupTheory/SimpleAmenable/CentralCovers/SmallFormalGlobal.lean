import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.LocalAtomComparison
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FullAlphabetGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SmallFormalGlobal
variable {α ι Ω H : Type*} [Fintype α] [DecidableEq α] [Finite ι] [Finite Ω] [Group H]

theorem smallFamily_assignment_law
    (U : ι → Set Ω) (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω=ν)
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hlaw : ∀ S : Finset α, S.card≤15 → ∀ w ∈ smallFamilyLocal (ι := ι) S,
      smallFamilyModel U w=1 → ∀ v ∈ smallFamilyLocal (ι := ι) S,
      Commute (smallFamilyEval F w) (smallFamilyEval F v))
    (hα : 5≤Fintype.card α) :
    HasCentralLaw (smallFamilyModel U) (smallFamilyEval F).rangeRestrict := by
  classical
  let e := smallFamilyEval F
  let v := smallFamilyModel (α := α) U
  let : Group.IsPerfect e.range := smallFamilyEval_perfect F
  obtain ⟨E,_hEsub,hE⟩ := Finset.exists_subset_card_eq
    (show 5≤(Finset.univ : Finset α).card by simpa using hα)
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<E.card by omega)
  obtain ⟨y,hy,hyx⟩ := Finset.exists_mem_ne (show 1<E.card by omega) x
  let a : SwapLabel α := ⟨Equiv.swap x y,x,y,Ne.symm hyx,rfl⟩
  have ha : a.val.support⊆E := by
    change (Equiv.swap x y).support⊆E
    rw [Equiv.Perm.support_swap (Ne.symm hyx)]
    exact Finset.insert_subset_iff.mpr ⟨hx,Finset.singleton_subset_iff.mpr hy⟩
  refine small_support_assignment_law (smallFamilyLocal (ι := ι)) smallFamilyLocal_mono
    v e.rangeRestrict e.rangeRestrict_surjective smallFamilyLocal_generate
    (smallFamilyModel_support U) ?_ E hE a ha ?_
  · intro S hS d hd hv z hz
    apply Commute.of_map (f := e.range.subtype) Subtype.val_injective
    exact hlaw S hS d hd hv z hz
  · intro S hS _ g hg
    exact smallFamilyModel_complete U hsep S hS g hg

theorem smallFamily_formal_quotient
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hlaw : ∀ S : Finset α, S.card≤15 → ∀ w ∈ smallFamilyLocal (ι := ι) S,
      smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}) w=1 →
      ∀ v ∈ smallFamilyLocal (ι := ι) S,
      Commute (smallFamilyEval F w) (smallFamilyEval F v))
    (hα : 5≤Fintype.card α) :
    ∃ φ : ((ι → Bool) → alternatingGroup α) →*
      ((smallFamilyEval F).range ⧸ Subgroup.center (smallFamilyEval F).range),
      Function.Surjective φ ∧
      φ.comp (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true})) =
        (QuotientGroup.mk' _).comp (smallFamilyEval F).rangeRestrict := by
  classical
  have hs : ∀ σ τ : ι → Bool,
      (∀ i, σ ∈ {σ : ι → Bool | σ i=true} ↔ τ ∈ {σ : ι → Bool | σ i=true}) → σ=τ := by
    intro σ τ h
    funext i
    exact Bool.eq_iff_iff.mpr (h i)
  have h := smallFamily_assignment_law _ hs F hlaw hα
  obtain ⟨φ,hφ⟩ := (hasCentralLaw_iff_modelMap _ _
    (smallFamilyModel_surjective _ hs hα)).mp h
  exact ⟨φ,centralLaw_modelMap_surjective _ _ (smallFamilyEval F).rangeRestrict_surjective φ hφ,hφ⟩

end SmallFormalGlobal

end SimpleAmenable
end
end

end OAI
