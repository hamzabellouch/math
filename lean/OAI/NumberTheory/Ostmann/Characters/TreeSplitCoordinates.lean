import Mathlib.Logic.Equiv.Prod
import OAI.NumberTheory.Ostmann.Characters.TreeLeafProducts
import OAI.NumberTheory.Ostmann.Arithmetic.SequentialSupport

namespace OAI

/-! # Independent split coordinates on each actual leaf-product fiber -/

namespace Ostmann

open scoped BigOperators Classical

def splitSamplesAppendEquiv (A : Type) : (m n : ℕ) →
    SplitSamples A (m + n) ≃ SplitSamples A m × SplitSamples A n
  | 0, n => by
      let e : SplitSamples A n ≃ Unit × SplitSamples A n :=
        { toFun := fun x => ((), x)
          invFun := Prod.snd
          left_inv := fun _ => rfl
          right_inv := fun x => by rcases x with ⟨u, x⟩; cases u; rfl }
      simpa only [Nat.zero_add, SplitSamples] using e
  | m + 1, n => by
      have e := (Equiv.prodCongr (Equiv.refl A) (splitSamplesAppendEquiv A m n)).trans
        (Equiv.prodAssoc A (SplitSamples A m) (SplitSamples A n)).symm
      simpa only [Nat.succ_add, SplitSamples] using e

/-- Preorder split products are coordinates: root split first, followed by
the left subtree and the right subtree. Each coordinate is an independent
Haar unit even after the total leaf product is fixed. -/
noncomputable def treeLeafSplitEquiv {G : Type} [CommGroup G] : (n : ℕ) → (P : G) →
    TreeLeafFiber G n P ≃ SplitSamples G (2 ^ n - 1)
  | 0, P => treeLeafFiberZeroEquiv P
  | n + 1, P => by
      let k := 2 ^ n - 1
      let e : TreeLeafFiber G (n + 1) P ≃ G × (SplitSamples G k × SplitSamples G k) :=
        (treeLeafFiberSuccEquiv n P).trans
          ((Equiv.sigmaCongrRight fun m =>
            Equiv.prodCongr (treeLeafSplitEquiv n m) (treeLeafSplitEquiv n (P / m))).trans
              (Equiv.sigmaEquivProd G (SplitSamples G k × SplitSamples G k)))
      have hcount : 2 ^ (n + 1) - 1 = k + k + 1 := by
        have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        dsimp [k]
        rw [pow_succ]
        omega
      have e' := e.trans (Equiv.prodCongr (Equiv.refl G) (splitSamplesAppendEquiv G k k).symm)
      simpa only [hcount, SplitSamples] using e'

/-- Exact transport of the original conditional Haar average. -/
theorem treeLeafSplit_average {G : Type} [CommGroup G] [Fintype G]
    (n : ℕ) (P : G) (F : SplitSamples G (2 ^ n - 1) → ℝ) :
    (Fintype.card (TreeLeafFiber G n P) : ℝ)⁻¹ *
        (∑ x : TreeLeafFiber G n P, F (treeLeafSplitEquiv n P x)) =
      (Fintype.card G : ℝ)⁻¹ ^ (2 ^ n - 1) * ∑ y, F y := by
  rw [(treeLeafSplitEquiv n P).sum_comp, card_treeLeafFiber, Nat.cast_pow, inv_pow]

/-- Adaptive support bounds therefore apply to the actual uniformly
sampled leaves with their product fixed, before any validity restriction. -/
theorem treeLeaf_sequentialSupport_le {G : Type} [CommGroup G] [Fintype G]
    (test : List G → G → Prop) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (htest : ∀ past, (Fintype.card G : ℝ)⁻¹ *
      (∑ x : G, if test past x then (1 : ℝ) else 0) ≤ ρ)
    (past : List G) (n : ℕ) (P : G) :
    (Fintype.card (TreeLeafFiber G n P) : ℝ)⁻¹ *
        (∑ x : TreeLeafFiber G n P,
          sequentialSupport test past (2 ^ n - 1) (treeLeafSplitEquiv n P x)) ≤
      ρ ^ (2 ^ n - 1) := by
  rw [treeLeafSplit_average]
  exact sequentialSupport_average_le test ρ hρ htest past (2 ^ n - 1)

end Ostmann

end OAI
