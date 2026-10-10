import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OAI.NumberTheory.Ostmann.Tree.ComponentFibers

namespace OAI

/-! # Simultaneous product fibers for an arbitrary partition of the leaves -/

namespace Ostmann

open scoped BigOperators

noncomputable def partitionProduct {L C G : Type*} [Fintype L] [DecidableEq C]
    [CommGroup G] (component : L → C) (m : L → G) (c : C) : G :=
  ∏ i : {i : L // component i = c}, m i.1

noncomputable def partitionCoordinates {L C G : Type*}
    (component : L → C) : (L → G) ≃ (∀ c : C, {i : L // component i = c} → G) :=
  Equiv.piCongrFiberwise (fun _ => Equiv.refl _)

/-- Fixing all component totals is the product of the individual product fibers. -/
noncomputable def partitionProductFiberEquiv {L C G : Type*}
    [Fintype L] [DecidableEq C] [CommGroup G]
    (component : L → C) (P : C → G) :
    {m : L → G // partitionProduct component m = P} ≃
      (∀ c : C, {v : ({i : L // component i = c} → G) // ∏ i, v i = P c}) where
  toFun m c := ⟨fun i => m.1 i.1, congrFun m.property c⟩
  invFun v := ⟨(partitionCoordinates component).symm (fun c => (v c).1), by
    funext c
    change (∏ i : {i : L // component i = c},
      ((partitionCoordinates component).symm (fun d => (v d).1)) i.1) = P c
    have h := congrFun ((partitionCoordinates component).apply_symm_apply
      (fun d => (v d).1)) c
    change (fun i : {i : L // component i = c} =>
      ((partitionCoordinates component).symm (fun d => (v d).1)) i.1) = (v c).1 at h
    rw [h]
    exact (v c).property⟩
  left_inv m := by
    apply Subtype.ext
    exact (partitionCoordinates component).symm_apply_apply m.1
  right_inv v := by
    funext c
    apply Subtype.ext
    exact congrFun ((partitionCoordinates component).apply_symm_apply
      (fun d => (v d).1)) c

theorem sum_card_partition {L C : Type*} [Fintype L] [Fintype C]
    [DecidableEq C] (component : L → C) :
    (∑ c : C, Fintype.card {i : L // component i = c}) = Fintype.card L := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv component)

theorem card_partitionProductFiber {L C G : Type*}
    [Fintype L] [Fintype C] [DecidableEq L] [DecidableEq C]
    [CommGroup G] [Fintype G] [DecidableEq G]
    (component : L → C) (pivot : ∀ c, {i : L // component i = c}) (P : C → G) :
    Fintype.card {m : L → G // partitionProduct component m = P} =
      Fintype.card G ^ (Fintype.card L - Fintype.card C) := by
  classical
  rw [Fintype.card_congr (partitionProductFiberEquiv component P), Fintype.card_pi]
  have hcard (c : C) :
      Fintype.card {i : {i : L // component i = c} // i ≠ pivot c} =
        Fintype.card {i : L // component i = c} - 1 := by
    simp only [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  simp_rw [card_componentProduct (pivot _), hcard]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.sum_tsub_distrib]
  · simp only [sum_card_partition, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, Nat.cast_id]
  · intro c _
    exact Fintype.card_pos_iff.mpr ⟨pivot c⟩

theorem card_partitionProduct_filter {L C G : Type*}
    [Fintype L] [Fintype C] [DecidableEq L] [DecidableEq C]
    [CommGroup G] [Fintype G] [DecidableEq G]
    (component : L → C) (pivot : ∀ c, {i : L // component i = c}) (P : C → G) :
    (Finset.univ.filter fun m : L → G => partitionProduct component m = P).card =
      Fintype.card G ^ (Fintype.card L - Fintype.card C) := by
  rw [← Fintype.card_subtype]
  exact card_partitionProductFiber component pivot P

end Ostmann

end OAI
