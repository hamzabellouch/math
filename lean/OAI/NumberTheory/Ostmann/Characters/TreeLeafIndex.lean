import Mathlib.Logic.Equiv.Prod
import OAI.NumberTheory.Ostmann.Tree.RationalTreeLeaves

namespace OAI

/-! # Labeled leaves and bottom quartets of a full binary tree -/

namespace Ostmann

open scoped BigOperators

def TreeLeafIndex : ℕ → Type
  | 0 => Unit
  | n + 1 => TreeLeafIndex n ⊕ TreeLeafIndex n

instance treeLeafIndexFintype (n : ℕ) : Fintype (TreeLeafIndex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact @instFintypeSum _ _ ih ih

instance treeLeafIndexDecidableEq (n : ℕ) : DecidableEq (TreeLeafIndex n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih => exact @instDecidableEqSum _ _ ih ih

instance treeLeafIndexNonempty (n : ℕ) : Nonempty (TreeLeafIndex n) := by
  induction n with
  | zero => exact ⟨()⟩
  | succ n ih => exact ⟨Sum.inl (Classical.choice ih)⟩

def treeLeafTupleEquiv (A : Type*) : (n : ℕ) →
    TreeLeafTuple A n ≃ (TreeLeafIndex n → A)
  | 0 =>
    { toFun := fun a _ => a
      invFun := fun f => f ()
      left_inv := fun _ => rfl
      right_inv := fun f => by funext u; cases u; rfl }
  | n + 1 => (Equiv.prodCongr (treeLeafTupleEquiv A n) (treeLeafTupleEquiv A n)).trans
      (Equiv.sumArrowEquivProdArrow (TreeLeafIndex n) (TreeLeafIndex n) A).symm

theorem card_treeLeafIndex (n : ℕ) : Fintype.card (TreeLeafIndex n) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (TreeLeafIndex n ⊕ TreeLeafIndex n) = _
    rw [Fintype.card_sum, ih, pow_succ]
    omega

def bottomQuartet : (n : ℕ) → TreeLeafIndex (n + 2) → TreeLeafIndex n
  | 0, _ => ()
  | n + 1, .inl i => .inl (bottomQuartet n i)
  | n + 1, .inr i => .inr (bottomQuartet n i)

noncomputable def indexedRationalAmplitude {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool n) (m : TreeLeafIndex n → (ZMod p)ˣ) : ℂ :=
  rationalTreeAmplitude g D T XL XR c ((treeLeafTupleEquiv (ZMod p)ˣ n).symm m)

theorem indexedRationalAmplitude_l2_bound {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool n) :
    (∑ m : TreeLeafIndex n → (ZMod p)ˣ, ‖indexedRationalAmplitude g D T XL XR c m‖ ^ 2) /
      (Fintype.card (TreeLeafIndex n → (ZMod p)ˣ) : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  have hsum := (treeLeafTupleEquiv (ZMod p)ˣ n).symm.sum_comp
    (fun m => ‖rationalTreeAmplitude g D T XL XR c m‖ ^ 2)
  have hcard := Fintype.card_congr (treeLeafTupleEquiv (ZMod p)ˣ n)
  change (∑ m : TreeLeafIndex n → (ZMod p)ˣ,
    ‖rationalTreeAmplitude g D T XL XR c ((treeLeafTupleEquiv (ZMod p)ˣ n).symm m)‖ ^ 2) /
    (Fintype.card (TreeLeafIndex n → (ZMod p)ˣ) : ℝ) ≤ _
  rw [hsum, ← hcard]
  exact rationalTreeAmplitude_l2_bound hp g hg henergy D T XL XR c

end Ostmann

end OAI
