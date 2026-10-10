import Mathlib.Logic.Equiv.Sum
import OAI.NumberTheory.Ostmann.Tree.ProductFibers

namespace OAI

/-! # Leaf-product fibers in a full binary tree -/

namespace Ostmann

open scoped BigOperators

@[implicit_reducible] def TreeLeafTuple (U : Type*) : ℕ → Type _
  | 0 => U
  | n + 1 => TreeLeafTuple U n × TreeLeafTuple U n

instance treeLeafTupleFintype (U : Type*) [Fintype U] (n : ℕ) : Fintype (TreeLeafTuple U n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype U)
  | succ n ih => exact @instFintypeProd _ _ ih ih

@[implicit_reducible] def treeLeafProduct {U : Type*} [CommMonoid U] : (n : ℕ) → TreeLeafTuple U n → U
  | 0, x => x
  | n + 1, xy => treeLeafProduct n xy.1 * treeLeafProduct n xy.2

abbrev TreeLeafFiber (U : Type*) [CommGroup U] (n : ℕ) (P : U) :=
  {x : TreeLeafTuple U n // treeLeafProduct n x = P}

noncomputable instance treeLeafFiberFintype (U : Type*) [CommGroup U] [Fintype U]
    (n : ℕ) (P : U) : Fintype (TreeLeafFiber U n P) := by
  classical
  unfold TreeLeafFiber
  infer_instance

def treeLeafFiberZeroEquiv {U : Type*} [CommGroup U] (P : U) :
    TreeLeafFiber U 0 P ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨P, rfl⟩
  left_inv x := Subtype.ext x.property.symm
  right_inv x := by cases x; rfl

/-- Exposing the product in the left half leaves independent product fibers below it. -/
def treeLeafFiberSuccEquiv {U : Type*} [CommGroup U] (n : ℕ) (P : U) :
    TreeLeafFiber U (n + 1) P ≃
      Σ m : U, TreeLeafFiber U n m × TreeLeafFiber U n (P / m) where
  toFun x := ⟨treeLeafProduct n x.1.1, ⟨x.1.1, rfl⟩, ⟨x.1.2, by
    calc
      _ = (treeLeafProduct n x.1.1 * treeLeafProduct n x.1.2) /
          treeLeafProduct n x.1.1 := (mul_div_cancel_left _ _).symm
      _ = _ := congrArg (fun t => t / treeLeafProduct n x.1.1) x.property⟩⟩
  invFun x := ⟨(x.2.1.1, x.2.2.1), by
    change treeLeafProduct n x.2.1.1 * treeLeafProduct n x.2.2.1 = P
    rw [x.2.1.property, x.2.2.property]
    exact mul_div_cancel _ _⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨m, ⟨a, ha⟩, ⟨b, hb⟩⟩
    dsimp at ha hb ⊢
    subst m
    rfl

theorem card_treeLeafTuple {U : Type*} [Fintype U] (n : ℕ) :
    Fintype.card (TreeLeafTuple U n) = Fintype.card U ^ (2 ^ n) := by
  induction n with
  | zero =>
    change Fintype.card U = Fintype.card U ^ (2 ^ 0)
    simp
  | succ n ih =>
    change Fintype.card (TreeLeafTuple U n × TreeLeafTuple U n) = _
    rw [Fintype.card_prod, ih, pow_succ (2 : ℕ), pow_mul, pow_two]

theorem card_treeLeafFiber {U : Type*} [CommGroup U] [Fintype U] (n : ℕ) (P : U) :
    Fintype.card (TreeLeafFiber U n P) = Fintype.card U ^ (2 ^ n - 1) := by
  induction n generalizing P with
  | zero => rw [Fintype.card_congr (treeLeafFiberZeroEquiv P)]; simp
  | succ n ih =>
    rw [Fintype.card_congr (treeLeafFiberSuccEquiv n P), Fintype.card_sigma]
    simp only [Fintype.card_prod, ih, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.cast_id]
    rw [← pow_add, ← pow_succ']
    congr 1
    have h : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    rw [pow_succ]
    omega

theorem sum_treeLeafFiber_succ {U R : Type*} [CommGroup U] [Fintype U]
    [AddCommMonoid R] (n : ℕ) (P : U) (f : TreeLeafTuple U (n + 1) → R) :
    (∑ x : TreeLeafFiber U (n + 1) P, f x.1) =
      ∑ m : U, ∑ a : TreeLeafFiber U n m, ∑ b : TreeLeafFiber U n (P / m),
        f (a.1, b.1) := by
  have h := (treeLeafFiberSuccEquiv n P).symm.sum_comp (fun x => f x.1)
  change (∑ x : (Σ m : U, TreeLeafFiber U n m × TreeLeafFiber U n (P / m)),
    f (x.2.1.1, x.2.2.1)) = _ at h
  simpa only [Fintype.sum_sigma, Fintype.sum_prod_type] using h.symm

theorem sum_treeLeafTuple_by_product {U R : Type*} [CommGroup U] [Fintype U]
    [AddCommMonoid R] (n : ℕ) (f : TreeLeafTuple U n → R) :
    (∑ x : TreeLeafTuple U n, f x) = ∑ P : U, ∑ x : TreeLeafFiber U n P, f x.1 := by
  classical
  have h := (Equiv.sigmaFiberEquiv (treeLeafProduct (U := U) n)).sum_comp f
  change (∑ x : (Σ P : U, TreeLeafFiber U n P), f x.2.1) = _ at h
  simpa only [Fintype.sum_sigma] using h.symm

end Ostmann

end OAI
