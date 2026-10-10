import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocalVirtualSolvabilityBound
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteSolvableDerivedBound
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedSolvableRadical

namespace OAI

/-! # A characteristic soluble subgroup for the locally virtually nilpotent kernel -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem virtuallyNilpotent_of_mulEquiv {J : Type} [Group J] (e : G ≃* J)
    (hG : Group.IsVirtuallyNilpotent G) : Group.IsVirtuallyNilpotent J := by
  obtain ⟨N, hN, hNi⟩ := hG
  let := hN
  let := hNi
  let f := N.equivMapOfInjective e.toMonoidHom e.injective
  exact ⟨N.map e.toMonoidHom, Group.nilpotent_of_mulEquiv f,
    Subgroup.FiniteIndex.map_of_surjective N e.surjective⟩

theorem locallyVirtuallyNilpotent_subgroup
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsVirtuallyNilpotent H) (S : Subgroup G) :
    ∀ H : Subgroup S, H.FG → Group.IsVirtuallyNilpotent H := by
  intro H hH
  exact virtuallyNilpotent_of_mulEquiv
    (H.equivMapOfInjective S.subtype Subtype.val_injective).symm
    (hlocal (H.map S.subtype) (fg_subgroup_map hH S.subtype))

theorem finiteSubgroupOrders_le_subgroup (b : ℕ)
    (hb : ∀ N : Subgroup G, Finite N → Nat.card N ≤ b) (S : Subgroup G) :
    ∀ N : Subgroup S, Finite N → Nat.card N ≤ b := by
  intro N hN
  let := hN
  let e := N.equivMapOfInjective S.subtype Subtype.val_injective
  let : Finite (N.map S.subtype) := Finite.of_equiv N e.toEquiv
  simpa only [Nat.card_congr e.toEquiv] using hb (N.map S.subtype) inferInstance

theorem locallyVirtuallyNilpotent_solvable_derived_bound [Group.IsSolvable G]
    (b d : ℕ) (hd : RationalHomologyDimensionLE G d)
    (hb : ∀ N : Subgroup G, Finite N → Nat.card N ≤ b)
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsVirtuallyNilpotent H) :
    derivedSeries G ((virtualSolvabilityIndexBound b d).factorial + (2 * d + 2)) = ⊥ := by
  obtain ⟨H, hHi, hHb, hHr⟩ := locallyVirtuallyNilpotent_bounded_solvable_subgroup b d hd hb hlocal
  let := hHi
  exact solvable_derivedSeries_bound_of_finiteIndex H _ _ hHb hHr

theorem locallyVirtuallyNilpotent_characteristic_solvable
    (d : ℕ) (hd : RationalHomologyDimensionLE G d) (hb : HasBoundedFiniteSubgroupOrders G)
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsVirtuallyNilpotent H) :
    ∃ R : Subgroup G, R.Characteristic ∧ R.FiniteIndex ∧ Group.IsSolvable R := by
  obtain ⟨b, hb⟩ := hb
  let r := (virtualSolvabilityIndexBound b d).factorial + (2 * d + 2)
  obtain ⟨R, hRchar, hRs, hmax⟩ := exists_characteristic_solvable_radical_of_bound r (by
    intro S hS
    let := hS
    exact locallyVirtuallyNilpotent_solvable_derived_bound b d (hd.subgroup S)
      (finiteSubgroupOrders_le_subgroup b hb S) (locallyVirtuallyNilpotent_subgroup hlocal S))
  obtain ⟨H, hHi, _, hHr⟩ := locallyVirtuallyNilpotent_bounded_solvable_subgroup b d hd hb hlocal
  let := hHi
  let : Group.IsSolvable H := ⟨2 * d + 2, hHr⟩
  have hNs : Group.IsSolvable H.normalCore :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion H.normalCore_le) (Subgroup.inclusion_injective _)
  let : R.FiniteIndex := Subgroup.finiteIndex_of_le (hmax H.normalCore inferInstance hNs)
  exact ⟨R, hRchar, inferInstance, hRs⟩

end PolycyclicRecognition

end

end OAI
