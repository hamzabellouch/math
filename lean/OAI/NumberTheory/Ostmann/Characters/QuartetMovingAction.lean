import OAI.NumberTheory.Ostmann.Characters.QuartetLocalBounds
import OAI.NumberTheory.Ostmann.Characters.TreeTupleProfiles
import OAI.NumberTheory.Ostmann.Characters.CycleAction

namespace OAI

/-! # The actual reciprocal leaf action in the six quartet coordinates -/

namespace Ostmann

open scoped BigOperators

def scaleOneLeaf {U : Type*} [CommGroup U] (s : ℤ) (z m : U) : U := z ^ s * m

theorem scaleOneLeaf_mul {U : Type*} [CommGroup U] (δ s : ℤ) (z m : U) :
    scaleOneLeaf (δ * s) z m = scaleOneLeaf s (z ^ δ) m := by
  simp only [scaleOneLeaf, zpow_mul]

@[implicit_reducible] def treeLeafScale {U : Type*} [CommGroup U] : (n : ℕ) →
    TreeLeafTuple ℤ n → U → TreeLeafTuple U n → TreeLeafTuple U n
  | 0, s, z, m => scaleOneLeaf (U := U) s z m
  | n + 1, s, z, m => (treeLeafScale n s.1 z m.1, treeLeafScale n s.2 z m.2)

def quartetMovingSign : QuartetMovingCase → TreeLeafTuple ℤ 2
  | .cross left right =>
      (((if left then (-1, 0) else (0, -1)), (if right then (1, 0) else (0, 1))) :
        (ℤ × ℤ) × (ℤ × ℤ))
  | .leftPair => (((-1, 1), (0, 0)) : (ℤ × ℤ) × (ℤ × ℤ))
  | .rightPair => (((0, 0), (-1, 1)) : (ℤ × ℤ) × (ℤ × ℤ))

theorem treeLeafTupleEquiv_scale {U : Type*} [CommGroup U] (n : ℕ)
    (s : TreeLeafTuple ℤ n) (z : U) (m : TreeLeafTuple U n) :
    treeLeafTupleEquiv U n (treeLeafScale n s z m) =
      cycleMultiply (treeLeafTupleEquiv ℤ n s) z (treeLeafTupleEquiv U n m) := by
  funext i
  induction n with
  | zero => rfl
  | succ n ih =>
    cases i with
    | inl i => exact ih s.1 m.1 i
    | inr i => exact ih s.2 m.2 i

theorem quartetMovingLeaves_scale {U : Type*} [CommGroup U]
    (choice : QuartetMovingCase) (P a b r z : U) :
    treeLeafScale 2 (quartetMovingSign choice) z (quartetMovingLeaves choice P a b r) =
      quartetMovingLeaves choice P a b (z * r) := by
  cases choice with
  | cross left right =>
    cases left <;> cases right <;>
      simp [treeLeafScale, scaleOneLeaf, quartetMovingSign, quartetMovingLeaves, crossQuartetLeaves,
        crossLeftLeaves, crossRightLeaves, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  | leftPair =>
    simp [treeLeafScale, scaleOneLeaf, quartetMovingSign, quartetMovingLeaves, samePairLeftLeaves,
      div_eq_mul_inv, mul_assoc, mul_comm]
  | rightPair =>
    simp [treeLeafScale, scaleOneLeaf, quartetMovingSign, quartetMovingLeaves, samePairRightLeaves,
      div_eq_mul_inv, mul_assoc, mul_comm]

theorem treeLeafScale_map_mul {U : Type*} [CommGroup U] (n : ℕ)
    (δ : ℤ) (s : TreeLeafTuple ℤ n) (z : U) (m : TreeLeafTuple U n) :
    treeLeafScale n (treeLeafMap (fun a : ℤ => δ * a) n s) z m =
      treeLeafScale n s (z ^ δ) m := by
  induction n with
  | zero => exact scaleOneLeaf_mul (U := U) δ s z m
  | succ n ih => exact Prod.ext (ih s.1 m.1) (ih s.2 m.2)

theorem quartetMovingLeaves_scaled_sign {U : Type*} [CommGroup U]
    (choice : QuartetMovingCase) (δ : ℤ) (P a b r z : U) :
    treeLeafScale 2 (treeLeafMap (fun s : ℤ => δ * s) 2 (quartetMovingSign choice)) z
      (quartetMovingLeaves choice P a b r) =
      quartetMovingLeaves choice P a b (z ^ δ * r) := by
  rw [treeLeafScale_map_mul, quartetMovingLeaves_scale]

noncomputable def quartetMovingFiberEquiv {U : Type*} [CommGroup U]
    (choice : QuartetMovingCase) (P : U) : TreeLeafFiber U 2 P ≃ U × (U × U) :=
  match choice with
  | .cross left right => crossQuartetFiberEquiv left right P
  | .leftPair => samePairLeftFiberEquiv P
  | .rightPair => samePairRightFiberEquiv P

theorem quartetMovingFiberEquiv_symm {U : Type*} [CommGroup U]
    (choice : QuartetMovingCase) (P a b r : U) :
    ((quartetMovingFiberEquiv choice P).symm (a, b, r)).1 =
      quartetMovingLeaves choice P a b r := by
  cases choice with
  | cross left right => exact crossQuartetFiberEquiv_symm left right P a b r
  | leftPair => rfl
  | rightPair => rfl

theorem sum_quartetMovingFiber {U R : Type*} [CommGroup U] [Fintype U] [AddCommMonoid R]
    (choice : QuartetMovingCase) (P : U) (f : TreeLeafTuple U 2 → R) :
    (∑ m : TreeLeafFiber U 2 P, f m.1) =
      ∑ a : U, ∑ b : U, ∑ r : U, f (quartetMovingLeaves choice P a b r) := by
  have h := (quartetMovingFiberEquiv choice P).symm.bijective.sum_comp
    (fun m : TreeLeafFiber U 2 P => f m.1)
  simpa only [Fintype.sum_prod_type, quartetMovingFiberEquiv_symm] using h.symm

end Ostmann

end OAI
