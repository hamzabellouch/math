import OAI.NumberTheory.Ostmann.Characters.TreeLeafIndex
import OAI.NumberTheory.Ostmann.Tree.SamePairFiber

namespace OAI

/-! # Independent product fibers at the bottom quartet level -/

namespace Ostmann

open scoped BigOperators

@[implicit_reducible] def quartetBlockTupleEquiv (A : Type*) : (n : ℕ) →
    TreeLeafTuple A (n + 2) ≃ TreeLeafTuple (TreeLeafTuple A 2) n
  | 0 => Equiv.refl _
  | n + 1 => Equiv.prodCongr (quartetBlockTupleEquiv A n) (quartetBlockTupleEquiv A n)

theorem quartetBlockTupleEquiv_succ (A : Type*) (n : ℕ)
    (m : TreeLeafTuple A (n + 1 + 2)) :
    quartetBlockTupleEquiv A (n + 1) m =
      (quartetBlockTupleEquiv A n m.1, quartetBlockTupleEquiv A n m.2) := rfl

def quartetBlockEquiv (A : Type*) (n : ℕ) :
    TreeLeafTuple A (n + 2) ≃ (TreeLeafIndex n → TreeLeafTuple A 2) :=
  (quartetBlockTupleEquiv A n).trans (treeLeafTupleEquiv (TreeLeafTuple A 2) n)

def quartetProducts {U : Type*} [CommGroup U] (n : ℕ)
    (m : TreeLeafTuple U (n + 2)) : TreeLeafIndex n → U :=
  fun i => treeLeafProduct 2 (quartetBlockEquiv U n m i)

abbrev QuartetProductFiber (U : Type*) [CommGroup U] (n : ℕ) (P : TreeLeafIndex n → U) :=
  {m : TreeLeafTuple U (n + 2) // quartetProducts n m = P}

noncomputable instance quartetProductFiberFintype (U : Type*) [CommGroup U] [Fintype U]
    (n : ℕ) (P : TreeLeafIndex n → U) : Fintype (QuartetProductFiber U n P) := by
  classical
  unfold QuartetProductFiber
  infer_instance

/-- Given the bottom quartet products, their interiors are independent
uniform fibers; the maps do not depend on any tree parameters. -/
def quartetProductFiberEquiv {U : Type*} [CommGroup U] (n : ℕ) (P : TreeLeafIndex n → U) :
    QuartetProductFiber U n P ≃ ((i : TreeLeafIndex n) → TreeLeafFiber U 2 (P i)) where
  toFun m i := ⟨quartetBlockEquiv U n m.1 i, congrFun m.property i⟩
  invFun m := ⟨(quartetBlockEquiv U n).symm (fun i => (m i).1), by
    funext i
    change treeLeafProduct 2 (quartetBlockEquiv U n
      ((quartetBlockEquiv U n).symm (fun i => (m i).1)) i) = P i
    rw [Equiv.apply_symm_apply]
    exact (m i).property⟩
  left_inv m := by
    apply Subtype.ext
    exact (quartetBlockEquiv U n).symm_apply_apply m.1
  right_inv m := by
    funext i
    apply Subtype.ext
    exact congrFun ((quartetBlockEquiv U n).apply_symm_apply (fun i => (m i).1)) i

theorem quartetProductFiberEquiv_symm {U : Type*} [CommGroup U] (n : ℕ)
    (P : TreeLeafIndex n → U) (m : (i : TreeLeafIndex n) → TreeLeafFiber U 2 (P i))
    (i : TreeLeafIndex n) :
    quartetBlockEquiv U n ((quartetProductFiberEquiv n P).symm m).1 i = (m i).1 := by
  exact congrFun ((quartetBlockEquiv U n).apply_symm_apply (fun i => (m i).1)) i

theorem card_quartetProductFiber {U : Type*} [CommGroup U] [Fintype U]
    (n : ℕ) (P : TreeLeafIndex n → U) :
    Fintype.card (QuartetProductFiber U n P) = (Fintype.card U ^ 3) ^ (2 ^ n) := by
  rw [Fintype.card_congr (quartetProductFiberEquiv n P), Fintype.card_pi]
  simp only [card_treeLeafFiber, Nat.reducePow, Nat.reduceSub, Finset.prod_const,
    Finset.card_univ, card_treeLeafIndex]

theorem sum_quartetProductFiber_product {U : Type*} [CommGroup U] [Fintype U]
    (n : ℕ) (P : TreeLeafIndex n → U)
    (f : TreeLeafIndex n → TreeLeafTuple U 2 → ℝ) :
    (∑ m : QuartetProductFiber U n P,
      ∏ i : TreeLeafIndex n, f i (quartetBlockEquiv U n m.1 i)) =
      ∏ i : TreeLeafIndex n, ∑ m : TreeLeafFiber U 2 (P i), f i m.1 := by
  have h := (quartetProductFiberEquiv n P).symm.bijective.sum_comp
    (fun m : QuartetProductFiber U n P => ∏ i : TreeLeafIndex n, f i (quartetBlockEquiv U n m.1 i))
  simp only [quartetProductFiberEquiv_symm] at h
  rw [← h]
  exact (Fintype.prod_sum (fun i (m : TreeLeafFiber U 2 (P i)) => f i m.1)).symm

theorem average_quartetProductFiber_product {U : Type*} [CommGroup U] [Fintype U]
    (n : ℕ) (P : TreeLeafIndex n → U)
    (f : TreeLeafIndex n → TreeLeafTuple U 2 → ℝ) :
    (Fintype.card (QuartetProductFiber U n P) : ℝ)⁻¹ *
      (∑ m : QuartetProductFiber U n P,
        ∏ i : TreeLeafIndex n, f i (quartetBlockEquiv U n m.1 i)) =
      ∏ i : TreeLeafIndex n, (Fintype.card (TreeLeafFiber U 2 (P i)) : ℝ)⁻¹ *
        ∑ m : TreeLeafFiber U 2 (P i), f i m.1 := by
  rw [sum_quartetProductFiber_product, card_quartetProductFiber]
  simp only [card_treeLeafFiber, Nat.reducePow, Nat.reduceSub, Nat.cast_pow,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_treeLeafIndex,
    inv_pow]

theorem sum_treeLeafTuple_by_quartetProducts {U R : Type*} [CommGroup U] [Fintype U]
    [AddCommMonoid R] (n : ℕ) (f : TreeLeafTuple U (n + 2) → R) :
    (∑ m : TreeLeafTuple U (n + 2), f m) =
      ∑ P : TreeLeafIndex n → U, ∑ m : QuartetProductFiber U n P, f m.1 := by
  classical
  have h := (Equiv.sigmaFiberEquiv (quartetProducts (U := U) n)).sum_comp f
  change (∑ m : (Σ P : TreeLeafIndex n → U, QuartetProductFiber U n P), f m.2.1) = _ at h
  simpa only [Fintype.sum_sigma] using h.symm

end Ostmann

end OAI
