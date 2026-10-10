import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.AbelianAlternatives
import OAI.Probability.CriticalPercolation.LinearGroups.SolvableGrowth

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical IsMulCommutative

namespace CriticalPercolation.SparseGrowth

lemma infinite_fg_abelian_surjects_int (B : Type*) [CommGroup B] [Group.FG B]
    [Infinite B] : ∃ f : B →* Multiplicative ℤ, Surjective f := by
  rcases abelian_alternatives B with hf | ⟨f,hf,_⟩ | ⟨f,hf⟩
  · let _ := hf
    exact False.elim (_root_.not_finite B)
  · exact ⟨f,hf⟩
  · let p : Multiplicative (ℤ×ℤ) →* Multiplicative ℤ :=
      (AddMonoidHom.fst ℤ ℤ).toMultiplicative
    have hp : Surjective p := fun z => ⟨Multiplicative.ofAdd (z.toAdd,0),rfl⟩
    exact ⟨p.comp f,hp.comp hf⟩

lemma virtually_indicable_of_derivedSeries_eq_bot (n : ℕ) :
    ∀ (A : Type*) [Group A] [DecidableEq A], ∀ d : ℕ,
      HasPolynomialDegree A d → derivedSeries A n=⊥ → Infinite A →
      ∃ H : Subgroup A, H.FiniteIndex ∧
        ∃ f : H →* Multiplicative ℤ, Surjective f := by
  induction n with
  | zero =>
    intro A _ _ d hg hz hi
    have hs : Subsingleton A := by
      constructor
      intro x y
      have hx : x=1 := by simpa only [hz,Subgroup.mem_bot] using
        (show x∈derivedSeries A 0 from Subgroup.mem_top x)
      have hy : y=1 := by simpa only [hz,Subgroup.mem_bot] using
        (show y∈derivedSeries A 0 from Subgroup.mem_top y)
      exact hx.trans hy.symm
    exact False.elim (_root_.not_finite A)
  | succ n ih =>
    intro A _ _ d hg hz hi
    let _ := hg.fg
    let C := commutator A
    let _ : Group.FG C := (Group.fg_iff_subgroup_fg C).mpr hg.commutator_fg
    let Q := A ⧸ C
    let _ : IsMulCommutative Q :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
    rcases finite_or_infinite Q with hq | hq
    · let _ := hq
      let _ : C.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      have hc : Infinite C := by
        rcases finite_or_infinite C with hfin | hinf
        · let _ := hfin
          let _ : Finite A := (C.finite_iff_finite_and_finiteIndex).mpr ⟨hfin,inferInstance⟩
          exact False.elim (_root_.not_finite A)
        · exact hinf
      have hgC := hg.of_injective C.subtype Subtype.val_injective
      have hzC : derivedSeries C n=⊥ := by
        apply Subgroup.map_injective (f := C.subtype) Subtype.val_injective
        rw [Subgroup.map_bot,map_derivedSeries_commutator,hz]
      obtain ⟨H,hHi,f,hf⟩ := ih C d hgC hzC hc
      let _ := hHi
      let J := H.map C.subtype
      let e : H ≃* J := H.equivMapOfInjective C.subtype Subtype.val_injective
      have hJi : J.FiniteIndex := by
        constructor
        rw [Subgroup.index_map_subtype]
        exact mul_ne_zero hHi.index_ne_zero (inferInstance : C.FiniteIndex).index_ne_zero
      exact ⟨J,hJi,f.comp e.symm.toMonoidHom,hf.comp e.symm.surjective⟩
    · let _ := hq
      obtain ⟨f,hf⟩ := infinite_fg_abelian_surjects_int Q
      let e : (⊤ : Subgroup A) ≃* A := Subgroup.topEquiv
      exact ⟨⊤,inferInstance,(f.comp (QuotientGroup.mk' C)).comp e.toMonoidHom,
        hf.comp ((QuotientGroup.mk'_surjective C).comp e.surjective)⟩

theorem HasPolynomialDegree.virtually_indicable {A : Type*} [Group A] [DecidableEq A]
    {d : ℕ} (hg : HasPolynomialDegree A d) [Group.IsSolvable A] [Infinite A] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ f : H →* Multiplicative ℤ, Surjective f := by
  obtain ⟨n,hn⟩ := Group.IsSolvable.solvable (G := A)
  exact virtually_indicable_of_derivedSeries_eq_bot n A d hg hn inferInstance

end CriticalPercolation.SparseGrowth
end
end

end OAI
