import OAI.GroupTheory.PolycyclicRecognition.Algebra.InfiniteAbelianIntegerQuotient
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Solvable
import Mathlib.GroupTheory.Schreier

namespace OAI

/-! # Virtual integer quotients of infinite finitely generated solvable groups

If the abelianization is finite, its kernel has finite index and one less
derived step. Induction therefore finds an infinite abelian quotient in a
finite-index subgroup, and a free coordinate gives the required map to `ℤ`.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

theorem infinite_of_finiteIndex {G : Type*} [Group G] [Infinite G]
    (H : Subgroup G) [H.FiniteIndex] : Infinite H := by
  cases finite_or_infinite H with
  | inr h => exact h
  | inl h =>
    have : Finite G := (H.finite_iff_finite_and_finiteIndex).mpr ⟨h, inferInstance⟩
    exact (not_finite G).elim

theorem virtual_integer_quotient_of_derivedSeries_eq_bot (n : ℕ) :
    ∀ (G : Type*) [Group G] [Group.FG G] [Infinite G],
      derivedSeries G n = ⊥ →
      ∃ H : Subgroup G, H.FiniteIndex ∧
        ∃ q : H →* Multiplicative ℤ, Function.Surjective q := by
  induction n with
  | zero =>
    intro G _ _ _ hn
    have htop : (⊤ : Subgroup G) = ⊥ := hn
    have : Subsingleton G := by
      constructor
      intro x y
      have hx : x = 1 := by simpa only [← Subgroup.mem_bot, ← htop] using
        (Subgroup.mem_top x)
      have hy : y = 1 := by simpa only [← Subgroup.mem_bot, ← htop] using
        (Subgroup.mem_top y)
      exact hx.trans hy.symm
    exact (not_finite G).elim
  | succ n ih =>
    intro G _ _ _ hn
    let N := commutator G
    cases finite_or_infinite (G ⧸ N) with
    | inr hinf =>
      let := hinf
      obtain ⟨q, hq⟩ := infinite_fg_abelian_integer_quotient (G ⧸ N)
      let qG := q.comp (QuotientGroup.mk' N)
      have hqG : Function.Surjective qG := hq.comp (QuotientGroup.mk'_surjective N)
      refine ⟨⊤, inferInstance, qG.comp (⊤ : Subgroup G).subtype, ?_⟩
      intro z
      obtain ⟨g, hg⟩ := hqG z
      exact ⟨⟨g, Subgroup.mem_top g⟩, hg⟩
    | inl hfin =>
      let := hfin
      let : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      let : Infinite N := infinite_of_finiteIndex N
      have hnN : derivedSeries N n = ⊥ := by
        apply Subgroup.map_injective (f := N.subtype) Subtype.val_injective
        rw [Subgroup.map_bot, map_derivedSeries_commutator, hn]
      obtain ⟨K, hK, q, hq⟩ := ih N hnN
      let e := K.equivMapOfInjective N.subtype Subtype.val_injective
      refine ⟨K.map N.subtype, ⟨?_⟩, q.comp e.symm.toMonoidHom,
        hq.comp e.symm.surjective⟩
      rw [Subgroup.index_map_subtype]
      exact mul_ne_zero hK.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := N))

theorem infinite_fg_solvable_virtual_integer_quotient (G : Type*)
    [Group G] [Group.FG G] [Infinite G] [Group.IsSolvable G] :
    ∃ H : Subgroup G, H.FiniteIndex ∧
      ∃ q : H →* Multiplicative ℤ, Function.Surjective q := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := G)
  exact virtual_integer_quotient_of_derivedSeries_eq_bot n G hn

theorem infinite_fg_virtually_solvable_virtual_integer_quotient
    {G : Type*} [Group G] [Group.FG G] [Infinite G]
    (S : Subgroup G) [S.FiniteIndex] [Group.IsSolvable S] :
    ∃ H : Subgroup G, H.FiniteIndex ∧
      ∃ q : H →* Multiplicative ℤ, Function.Surjective q := by
  let : Infinite S := infinite_of_finiteIndex S
  obtain ⟨K, hK, q, hq⟩ := infinite_fg_solvable_virtual_integer_quotient S
  let e := K.equivMapOfInjective S.subtype Subtype.val_injective
  refine ⟨K.map S.subtype, ⟨?_⟩, q.comp e.symm.toMonoidHom,
    hq.comp e.symm.surjective⟩
  rw [Subgroup.index_map_subtype]
  exact mul_ne_zero hK.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := S))

end PolycyclicRecognition

end

end OAI
