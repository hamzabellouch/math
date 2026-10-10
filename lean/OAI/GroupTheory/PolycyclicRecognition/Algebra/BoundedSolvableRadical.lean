import OAI.GroupTheory.PolycyclicRecognition.Algebra.DirectedDerivedSeries
import Mathlib.Order.Zorn
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OAI

/-! # A characteristic solvable radical under a uniform derived-length bound -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem solvable_sup_of_normal (H K : Subgroup G) [H.Normal] [K.Normal]
    [Group.IsSolvable H] [Group.IsSolvable K] : Group.IsSolvable (H ⊔ K : Subgroup G) := by
  let S := K ⊔ H
  let N := H.subgroupOf S
  let e := Subgroup.subgroupOfEquivOfLe (show H ≤ S from le_sup_right)
  let : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let q := QuotientGroup.quotientInfEquivProdNormalQuotient K H
  let : Group.IsSolvable (S ⧸ N) :=
    Group.isSolvable_of_surjective (f := q.toMonoidHom) q.surjective
  have hs : Group.IsSolvable S := Group.isSolvable_of_subgroup_quotient N
  change Group.IsSolvable (K ⊔ H : Subgroup G) at hs
  rwa [sup_comm K H] at hs

theorem exists_characteristic_solvable_radical_of_bound (r : ℕ)
    (hbound : ∀ H : Subgroup G, Group.IsSolvable H → derivedSeries H r = ⊥) :
    ∃ R : Subgroup G, R.Characteristic ∧ Group.IsSolvable R ∧
      ∀ H : Subgroup G, H.Normal → Group.IsSolvable H → H ≤ R := by
  let P : Set (Subgroup G) := {H | H.Normal ∧ Group.IsSolvable H}
  obtain ⟨R, hR, hmax⟩ := zorn_le₀ P (by
    intro C hC hchain
    rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊥, ⟨inferInstance, inferInstance⟩, by simp⟩
    · have hn : (sSup C).Normal := Subgroup.sSup_normal C (fun H hH => (hC hH).1)
      have hs : Group.IsSolvable (sSup C : Subgroup G) :=
        ⟨r, sSup_derivedSeries_eq_bot C hne hchain.directedOn r
          (fun H hH => hbound H (hC hH).2)⟩
      exact ⟨sSup C, ⟨hn, hs⟩, fun H hH => le_sSup hH⟩)
  let := hR.1
  let := hR.2
  have hle (H : Subgroup G) (hn : H.Normal) (hs : Group.IsSolvable H) : H ≤ R := by
    let := hn
    let := hs
    have hj : Group.IsSolvable (R ⊔ H : Subgroup G) := solvable_sup_of_normal R H
    have he : R ⊔ H ≤ R := hmax ⟨inferInstance, hj⟩ le_sup_left
    exact le_sup_right.trans he
  have hchar : R.Characteristic := by
    apply Subgroup.characteristic_iff_map_le.mpr
    intro e
    have hs : Group.IsSolvable (R.map e.toMonoidHom) :=
      Group.isSolvable_of_surjective
        (f := (R.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
        (R.equivMapOfInjective e.toMonoidHom e.injective).surjective
    exact hle _ (Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective) hs
  exact ⟨R, hchar, hR.2, hle⟩

end PolycyclicRecognition

end

end OAI
