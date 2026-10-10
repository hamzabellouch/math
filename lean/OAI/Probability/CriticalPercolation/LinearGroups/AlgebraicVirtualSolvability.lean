import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.StrongAbstractSpan
import OAI.Probability.CriticalPercolation.LinearGroups.InvariantSubspaceDensity
import OAI.Probability.CriticalPercolation.LinearGroups.InvariantBlockSolvability
import OAI.Probability.CriticalPercolation.Nilpotent.CharacteristicNilpotentCore

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth

lemma finiteIndex_comap_surjective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Surjective f) (P : Subgroup B) [P.FiniteIndex] :
    (P.comap f).FiniteIndex := by
  constructor
  rw [Subgroup.index_comap,f.range_eq_top_of_surjective hf,Subgroup.relIndex_top_right]
  exact Subgroup.FiniteIndex.index_ne_zero

lemma solvable_range_of_mem {A B : Type*} [Group A] [Group B]
    (f : A →* B) (P : Subgroup B) [Group.IsSolvable P] (hp : ∀ a, f a∈P) :
    Group.IsSolvable f.range := by
  have hh : f.range≤P := by rintro _ ⟨a,rfl⟩; exact hp a
  exact Group.isSolvable_of_isSolvable_injective (f:=Subgroup.inclusion hh)
    (Subgroup.inclusion_injective hh)

lemma solvable_restricted_range {A B : Type*} [Group A] [Group B]
    (f : A →* B) (P : Subgroup f.range) [Group.IsSolvable P]
    (J : Subgroup A) (hJ : J≤P.comap f.rangeRestrict) :
    Group.IsSolvable (f.comp J.subtype).range := by
  let Q := P.map f.range.subtype
  let e := P.equivMapOfInjective f.range.subtype Subtype.val_injective
  let : Group.IsSolvable Q := Group.isSolvable_of_surjective (f:=e.toMonoidHom) e.surjective
  apply solvable_range_of_mem (f.comp J.subtype) Q
  intro j
  exact ⟨f.rangeRestrict j.val,hJ j.property,rfl⟩

lemma virtually_solvable_linear_of_rank (K : Type) [Field K] [CharZero K]
    [Countable K] [IsAlgClosed K] (r : ℕ) :
    ∀ (V G : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      [Group G] [DecidableEq G], finrank K V=r →
      ∀ (ρ : G →* (V ≃ₗ[K] V)), Injective ρ →
      ∀ d, SparseGrowth.HasPolynomialDegree G d →
      ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro V G _ _ _ _ _ hr ρ hρ d hg
    rcases subsingleton_or_nontrivial V with hv | hv
    · let := hv
      have hc : ∀ g h : G, g*h=h*g := by
        intro g h
        apply hρ
        exact Subsingleton.elim _ _
      let : Group.IsSolvable G := Group.isSolvable_of_comm hc
      exact ⟨⊤,inferInstance,inferInstance⟩
    let := hv
    by_cases hd : StrongFullSpan ρ
    · obtain ⟨H,hHi,hH⟩ := hd.virtually_comm_range ρ hg
      let : Group.IsSolvable (ρ.comp H.subtype).range := Group.isSolvable_of_comm hH
      have hinj : Injective (ρ.comp H.subtype).rangeRestrict := by
        intro x y he
        apply Subtype.ext
        apply hρ
        exact congrArg Subtype.val he
      exact ⟨H,hHi,Group.isSolvable_of_isSolvable_injective hinj⟩
    obtain ⟨H,hHi,hH⟩ : ∃ H : Subgroup G, H.FiniteIndex ∧ ¬FullSpan (ρ.comp H.subtype) := by
      simp only [StrongFullSpan,not_forall] at hd
      obtain ⟨H,hHi,hH⟩ := hd
      exact ⟨H,hHi,hH⟩
    let := hHi
    let ρH := ρ.comp H.subtype
    have hgH := hg.finiteIndex_subgroup H
    obtain ⟨W,hW0,hW1,hW⟩ := invariant_subspace_of_not_fullSpan ρH hH
    let σ := subspaceRepresentation ρH W hW
    let τ := quotientRepresentation ρH W hW
    have hWrank : finrank K W<r := hr ▸ Submodule.finrank_lt hW1
    have hQrank : finrank K (V ⧸ W)<r := by
      have he := W.finrank_quotient_add_finrank
      have hp : 0 < finrank K W := by
        let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
        exact Module.finrank_pos (R:=K) (M:=W)
      omega
    have hgσ := hgH.of_surjective σ.rangeRestrict σ.rangeRestrict_surjective
    have hgτ := hgH.of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
    obtain ⟨P,hPi,hPs⟩ := ih _ hWrank W σ.range rfl σ.range.subtype Subtype.val_injective d hgσ
    obtain ⟨Q,hQi,hQs⟩ := ih _ hQrank (V ⧸ W) τ.range rfl τ.range.subtype Subtype.val_injective d hgτ
    let := hPi
    let := hQi
    let := hPs
    let := hQs
    let J := P.comap σ.rangeRestrict ⊓ Q.comap τ.rangeRestrict
    let : (P.comap σ.rangeRestrict).FiniteIndex :=
      finiteIndex_comap_surjective σ.rangeRestrict σ.rangeRestrict_surjective P
    let : (Q.comap τ.rangeRestrict).FiniteIndex :=
      finiteIndex_comap_surjective τ.rangeRestrict τ.rangeRestrict_surjective Q
    let : J.FiniteIndex := inferInstance
    have hWJ (j : J) : W.map (ρH j.val).toLinearMap=W := hW j.val
    have hsJ : subspaceRepresentation (ρH.comp J.subtype) W hWJ=σ.comp J.subtype := by
      ext j w; rfl
    have htJ : quotientRepresentation (ρH.comp J.subtype) W hWJ=τ.comp J.subtype := by
      ext j v
      induction v using Submodule.Quotient.induction_on
      rfl
    let : Group.IsSolvable (subspaceRepresentation (ρH.comp J.subtype) W hWJ).range :=
      hsJ.symm ▸ solvable_restricted_range σ P J inf_le_left
    let : Group.IsSolvable (quotientRepresentation (ρH.comp J.subtype) W hWJ).range :=
      htJ.symm ▸ solvable_restricted_range τ Q J inf_le_right
    let : Group.IsSolvable J := solvable_of_subspace_quotient (ρH.comp J.subtype)
      ((hρ.comp Subtype.val_injective).comp Subtype.val_injective) W hWJ
    let L := J.map H.subtype
    let e := J.equivMapOfInjective H.subtype Subtype.val_injective
    have hLi : L.FiniteIndex := by
      constructor
      rw [Subgroup.index_map_subtype]
      exact mul_ne_zero (inferInstance : J.FiniteIndex).index_ne_zero hHi.index_ne_zero
    exact ⟨L,hLi,Group.isSolvable_of_surjective (f:=e.toMonoidHom) e.surjective⟩

lemma virtually_solvable_linear (K V G : Type) [Field K] [CharZero K]
    [Countable K] [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Group G] [DecidableEq G] (ρ : G →* (V ≃ₗ[K] V)) (hρ : Injective ρ)
    {degree : ℕ} (hg : SparseGrowth.HasPolynomialDegree G degree) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H :=
  virtually_solvable_linear_of_rank K (finrank K V) V G rfl ρ hρ degree hg

end CriticalPercolation.LinearGrowth
end
end

end OAI
