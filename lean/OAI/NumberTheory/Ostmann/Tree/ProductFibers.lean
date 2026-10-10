import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Uniform product fibers for pairs and quartets

These explicit bijections justify exposing a component product and then
using independent coordinates on its fiber in the tree comparison.
-/

namespace Ostmann

open scoped BigOperators

def fixedProductPairEquiv {G : Type*} [CommGroup G] (P : G) :
    {xy : G × G // xy.1 * xy.2 = P} ≃ G where
  toFun xy := xy.1.1
  invFun x := ⟨(x, P / x), by simp⟩
  left_inv xy := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change P / xy.1.1 = xy.1.2
      calc
        _ = (xy.1.1 * xy.1.2) / xy.1.1 := congrArg (fun t => t / xy.1.1) xy.property.symm
        _ = _ := mul_div_cancel_left _ _
  right_inv x := rfl

def fixedProductQuartetEquiv {G : Type*} [CommGroup G] (P : G) :
    {m : G × (G × (G × G)) // m.1 * m.2.1 * m.2.2.1 * m.2.2.2 = P} ≃ G × (G × G) where
  toFun m := (m.1.1, m.1.2.1, m.1.2.2.1)
  invFun xyz := ⟨(xyz.1, xyz.2.1, xyz.2.2, P / (xyz.1 * xyz.2.1 * xyz.2.2)), by
    dsimp
    exact mul_div_cancel _ _⟩
  left_inv m := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · change P / (m.1.1 * m.1.2.1 * m.1.2.2.1) = m.1.2.2.2
          calc
            _ = (m.1.1 * m.1.2.1 * m.1.2.2.1 * m.1.2.2.2) /
                (m.1.1 * m.1.2.1 * m.1.2.2.1) :=
              congrArg (fun t => t / (m.1.1 * m.1.2.1 * m.1.2.2.1)) m.property.symm
            _ = _ := mul_div_cancel_left _ _
  right_inv xyz := rfl

theorem card_fixedProductPair {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] (P : G) :
    Fintype.card {xy : G × G // xy.1 * xy.2 = P} = Fintype.card G :=
  Fintype.card_congr (fixedProductPairEquiv P)

theorem card_fixedProductQuartet {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] (P : G) :
    Fintype.card {m : G × (G × (G × G)) // m.1 * m.2.1 * m.2.2.1 * m.2.2.2 = P} =
      (Fintype.card G) ^ 3 := by
  rw [Fintype.card_congr (fixedProductQuartetEquiv P), Fintype.card_prod, Fintype.card_prod]
  ring

/-- Uniform sampling of a fixed pair product leaves one free group coordinate. -/
theorem sum_fixedProductPair {G R : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    [AddCommMonoid R] (P : G) (f : G × G → R) :
    (∑ xy : {xy : G × G // xy.1 * xy.2 = P}, f xy.1) = ∑ x : G, f (x, P / x) := by
  exact ((fixedProductPairEquiv P).symm.bijective.sum_comp (fun xy => f xy.1)).symm

/-- A fixed quartet product leaves three independent free coordinates. -/
theorem sum_fixedProductQuartet {G R : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    [AddCommMonoid R] (P : G) (f : G × (G × (G × G)) → R) :
    (∑ m : {m : G × (G × (G × G)) // m.1 * m.2.1 * m.2.2.1 * m.2.2.2 = P}, f m.1) =
      ∑ x : G, ∑ y : G, ∑ z : G, f (x, y, z, P / (x * y * z)) := by
  have h := (fixedProductQuartetEquiv P).symm.bijective.sum_comp (fun m => f m.1)
  change (∑ xyz : G × (G × G), f (xyz.1, xyz.2.1, xyz.2.2,
    P / (xyz.1 * xyz.2.1 * xyz.2.2))) = _ at h
  simpa only [Fintype.sum_prod_type] using h.symm

end Ostmann

end OAI
