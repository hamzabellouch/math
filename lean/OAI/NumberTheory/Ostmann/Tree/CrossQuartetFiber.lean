import OAI.NumberTheory.Ostmann.Characters.QuartetCrossBound

namespace OAI

/-! # Exact product-fiber coordinates for the cross-pair coefficient bounds -/

namespace Ostmann

open scoped BigOperators

local instance zeroTupleCommGroup {U : Type*} [CommGroup U] :
    CommGroup (TreeLeafTuple U 0) := inferInstanceAs (CommGroup U)

def pairOrient {U : Type*} (friendly : Bool) (xy : U × U) : U × U :=
  if friendly then xy else (xy.2, xy.1)

def quartetOrient {U : Type*} (left right : Bool) (m : (U × U) × (U × U)) :
    (U × U) × (U × U) := (pairOrient left m.1, pairOrient right m.2)

theorem pairOrient_product {U : Type*} [CommGroup U] (friendly : Bool) (xy : U × U) :
    (pairOrient friendly xy).1 * (pairOrient friendly xy).2 = xy.1 * xy.2 := by
  cases friendly <;> simp [pairOrient, mul_comm]

def quartetOrientFiberEquiv {U : Type*} [CommGroup U] (left right : Bool) (P : U) :
    TreeLeafFiber U 2 P ≃ TreeLeafFiber U 2 P where
  toFun m := ⟨quartetOrient left right m.1, by
    change (pairOrient left m.1.1).1 * (pairOrient left m.1.1).2 *
      ((pairOrient right m.1.2).1 * (pairOrient right m.1.2).2) = P
    rw [pairOrient_product, pairOrient_product]
    exact m.property⟩
  invFun m := ⟨quartetOrient left right m.1, by
    change (pairOrient left m.1.1).1 * (pairOrient left m.1.1).2 *
      ((pairOrient right m.1.2).1 * (pairOrient right m.1.2).2) = P
    rw [pairOrient_product, pairOrient_product]
    exact m.property⟩
  left_inv m := by
    apply Subtype.ext
    cases left <;> cases right <;> rfl
  right_inv m := by
    apply Subtype.ext
    cases left <;> cases right <;> rfl

private theorem fourth_of_product {U : Type*} [CommGroup U] (a b c d P : U)
    (h : (a * b) * (c * d) = P) : P * a⁻¹ / (b * d) = c := by
  apply (div_eq_iff_eq_mul).2
  apply (mul_inv_eq_iff_eq_mul).2
  calc
    P = (a * b) * (c * d) := h.symm
    _ = (c * (b * d)) * a := by ac_rfl

/-- The held coordinates and the inverse first free coordinate parametrize
one quartet product fiber without changing its uniform measure. -/
noncomputable def friendlyQuartetFiberEquiv {U : Type*} [CommGroup U] (P : U) :
    TreeLeafFiber U 2 P ≃ U × (U × U) where
  toFun m := (m.1.1.2, m.1.2.2, m.1.1.1⁻¹)
  invFun x := ⟨((x.2.2⁻¹, x.1), (P * x.2.2 / (x.1 * x.2.1), x.2.1)),
    quartet_friendly_product P x.1 x.2.1 x.2.2⟩
  left_inv m := by
    apply Subtype.ext
    apply Prod.ext
    · exact Prod.ext (inv_inv _) rfl
    · apply Prod.ext
      · exact fourth_of_product m.1.1.1 m.1.1.2 m.1.2.1 m.1.2.2 P m.property
      · rfl
  right_inv x := by
    change (x.1, x.2.1, (x.2.2⁻¹)⁻¹) = x
    simp only [inv_inv]

noncomputable def crossQuartetFiberEquiv {U : Type*} [CommGroup U]
    (left right : Bool) (P : U) : TreeLeafFiber U 2 P ≃ U × (U × U) :=
  (quartetOrientFiberEquiv left right P).trans (friendlyQuartetFiberEquiv P)

theorem crossQuartetFiberEquiv_symm {U : Type*} [CommGroup U]
    (left right : Bool) (P a b r : U) :
    ((crossQuartetFiberEquiv left right P).symm (a, b, r)).1 =
      crossQuartetLeaves left right P a b r := by
  cases left <;> cases right <;> rfl

/-- This is the actual uniform product-fiber measure used by the cycle proof. -/
theorem sum_crossQuartetFiber {U R : Type*} [CommGroup U] [Fintype U] [DecidableEq U]
    [AddCommMonoid R] (left right : Bool) (P : U) (f : TreeLeafTuple U 2 → R) :
    (∑ m : TreeLeafFiber U 2 P, f m.1) =
      ∑ a : U, ∑ b : U, ∑ r : U, f (crossQuartetLeaves left right P a b r) := by
  have h := (crossQuartetFiberEquiv left right P).symm.bijective.sum_comp
    (fun m : TreeLeafFiber U 2 P => f m.1)
  simp only [crossQuartetFiberEquiv_symm, Fintype.sum_prod_type] at h
  exact h.symm

theorem mean_crossQuartetFiber {U : Type*} [CommGroup U] [Fintype U] [DecidableEq U]
    (left right : Bool) (P : U) (f : TreeLeafTuple U 2 → ℝ) :
    (Fintype.card (TreeLeafFiber U 2 P) : ℝ)⁻¹ * (∑ m : TreeLeafFiber U 2 P, f m.1) =
      (Fintype.card U : ℝ)⁻¹ * (∑ a : U, (Fintype.card U : ℝ)⁻¹ *
        (∑ b : U, (Fintype.card U : ℝ)⁻¹ *
          ∑ r : U, f (crossQuartetLeaves left right P a b r))) := by
  rw [sum_crossQuartetFiber left right P f, card_treeLeafFiber]
  norm_num only [Nat.reducePow, Nat.reduceSub, Nat.cast_pow]
  simp only [← Finset.mul_sum]
  ring

end Ostmann

end OAI
