import OAI.NumberTheory.Ostmann.Characters.QuartetSamePairBound
import OAI.NumberTheory.Ostmann.Tree.CrossQuartetFiber

namespace OAI

/-! # Exact product-fiber laws for the two same-pair parametrizations -/

namespace Ostmann

open scoped BigOperators

local instance samePairZeroTupleCommGroup {U : Type*} [CommGroup U] :
    CommGroup (TreeLeafTuple U 0) := inferInstanceAs (CommGroup U)

private theorem first_of_product {U : Type*} [CommGroup U] (a b c d P : U)
    (h : (a * b) * (c * d) = P) : P / ((c * d) * b) = a := by
  apply div_eq_iff_eq_mul.mpr
  exact h.symm.trans (by ac_rfl)

noncomputable def samePairLeftFiberEquiv {U : Type*} [CommGroup U] (P : U) :
    TreeLeafFiber U 2 P ≃ U × (U × U) where
  toFun m := ((m.1.2.1 : U) * m.1.2.2, m.1.2.2, m.1.1.2)
  invFun x := ⟨samePairLeftLeaves P x.1 x.2.1 x.2.2,
    samePair_total_product P x.1 x.2.1 x.2.2⟩
  left_inv m := by
    apply Subtype.ext
    apply Prod.ext
    · exact Prod.ext (first_of_product m.1.1.1 m.1.1.2 m.1.2.1 m.1.2.2 P m.property) rfl
    · exact Prod.ext (mul_div_cancel_right _ _) rfl
  right_inv x := by
    change ((x.1 / x.2.1) * x.2.1, x.2.1, x.2.2) = x
    simp only [div_mul_cancel]

private theorem third_of_product {U : Type*} [CommGroup U] (a b c d P : U)
    (h : (a * b) * (c * d) = P) : P * (a * b)⁻¹ / d = c := by
  apply div_eq_iff_eq_mul.mpr
  apply mul_inv_eq_iff_eq_mul.mpr
  exact h.symm.trans (by ac_rfl)

private theorem undo_pair_product {U : Type*} [CommGroup U] (a b : U) :
    ((a * b)⁻¹)⁻¹ / b = a := by rw [inv_inv, mul_div_cancel_right]

noncomputable def samePairRightFiberEquiv {U : Type*} [CommGroup U] (P : U) :
    TreeLeafFiber U 2 P ≃ U × (U × U) where
  toFun m := (((m.1.1.1 : U) * m.1.1.2)⁻¹, m.1.1.2, m.1.2.2)
  invFun x := ⟨samePairRightLeaves P x.1 x.2.1 x.2.2,
    samePair_right_total_product P x.1 x.2.1 x.2.2⟩
  left_inv m := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact undo_pair_product m.1.1.1 m.1.1.2
      · rfl
    · exact Prod.ext (third_of_product m.1.1.1 m.1.1.2 m.1.2.1 m.1.2.2 P m.property) rfl
  right_inv x := by
    change (((x.1⁻¹ / x.2.1) * x.2.1)⁻¹, x.2.1, x.2.2) = x
    simp only [div_mul_cancel, inv_inv]

theorem samePairLeftFiberEquiv_symm {U : Type*} [CommGroup U] (P a b r : U) :
    ((samePairLeftFiberEquiv P).symm (a, b, r)).1 = samePairLeftLeaves P a b r := rfl

theorem samePairRightFiberEquiv_symm {U : Type*} [CommGroup U] (P a b r : U) :
    ((samePairRightFiberEquiv P).symm (a, b, r)).1 = samePairRightLeaves P a b r := rfl

theorem sum_samePairLeftFiber {U R : Type*} [CommGroup U] [Fintype U]
    [AddCommMonoid R] (P : U) (f : TreeLeafTuple U 2 → R) :
    (∑ m : TreeLeafFiber U 2 P, f m.1) =
      ∑ a : U, ∑ b : U, ∑ r : U, f (samePairLeftLeaves P a b r) := by
  have h := (samePairLeftFiberEquiv P).symm.bijective.sum_comp
    (fun m : TreeLeafFiber U 2 P => f m.1)
  simpa only [Fintype.sum_prod_type, samePairLeftFiberEquiv_symm] using h.symm

theorem sum_samePairRightFiber {U R : Type*} [CommGroup U] [Fintype U]
    [AddCommMonoid R] (P : U) (f : TreeLeafTuple U 2 → R) :
    (∑ m : TreeLeafFiber U 2 P, f m.1) =
      ∑ a : U, ∑ b : U, ∑ r : U, f (samePairRightLeaves P a b r) := by
  have h := (samePairRightFiberEquiv P).symm.bijective.sum_comp
    (fun m : TreeLeafFiber U 2 P => f m.1)
  simpa only [Fintype.sum_prod_type, samePairRightFiberEquiv_symm] using h.symm

theorem mean_samePairLeftFiber {U : Type*} [CommGroup U] [Fintype U]
    (P : U) (f : TreeLeafTuple U 2 → ℝ) :
    (Fintype.card (TreeLeafFiber U 2 P) : ℝ)⁻¹ * (∑ m : TreeLeafFiber U 2 P, f m.1) =
      (Fintype.card U : ℝ)⁻¹ * (∑ a : U, (Fintype.card U : ℝ)⁻¹ *
        (∑ b : U, (Fintype.card U : ℝ)⁻¹ * ∑ r : U, f (samePairLeftLeaves P a b r))) := by
  rw [sum_samePairLeftFiber P f, card_treeLeafFiber]
  norm_num only [Nat.reducePow, Nat.reduceSub, Nat.cast_pow]
  simp only [← Finset.mul_sum]
  ring

end Ostmann

end OAI
