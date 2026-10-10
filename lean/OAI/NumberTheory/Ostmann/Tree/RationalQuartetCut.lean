import OAI.NumberTheory.Ostmann.Characters.QuartetProductFibers
import OAI.NumberTheory.Ostmann.Tree.RationalProfileLeaves

namespace OAI

/-! # Cutting an actual rational tree at its bottom quartets

The option-valued state records ancestor validity. On a valid cut each
state contains the original depth-two tree and its propagated current
entries. No quartet replacement or independence hypothesis is used.
-/

namespace Ostmann

open scoped BigOperators

@[implicit_reducible] def treeLeafMap {A B : Type*} (f : A → B) : (n : ℕ) →
    TreeLeafTuple A n → TreeLeafTuple B n
  | 0, a => f a
  | n + 1, a => (treeLeafMap f n a.1, treeLeafMap f n a.2)

def treeLeafZipProduct {A B R : Type*} [Mul R] (f : A → B → R) : (n : ℕ) →
    TreeLeafTuple A n → TreeLeafTuple B n → R
  | 0, a, b => f a b
  | n + 1, a, b => treeLeafZipProduct f n a.1 b.1 * treeLeafZipProduct f n a.2 b.2

theorem treeLeafProduct_quartetBlocks {U : Type*} [CommGroup U] (n : ℕ)
    (m : TreeLeafTuple U (n + 2)) :
    treeLeafProduct (n + 2) m = treeLeafProduct n
      (treeLeafMap (treeLeafProduct 2) n (quartetBlockTupleEquiv U n m)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change treeLeafProduct (n + 2) m.1 * treeLeafProduct (n + 2) m.2 = _
    rw [ih m.1, ih m.2]
    rfl

def RationalTreeData.cutTwo {U : Type*} [CommGroup U] : (n : ℕ) → {C : U} →
    RationalTreeData U (n + 2) C → RationalTreeData U n C
  | 0, C, T => .leaf T.frequency C
  | n + 1, _, .node s CL CR u left right =>
    .node s CL CR u (left.cutTwo n) (right.cutTwo n)

@[simp] theorem RationalTreeData.frequency_cutTwo {U : Type*} [CommGroup U]
    (n : ℕ) {C : U} (T : RationalTreeData U (n + 2) C) :
    (T.cutTwo n).frequency = T.frequency := by
  cases n with
  | zero => rfl
  | succ n => cases T; rfl

structure RationalQuartetState (p : ℕ) [Fact p.Prime] where
  C : (ZMod p)ˣ
  tree : RationalTreeData (ZMod p)ˣ 2 C
  XL : (ZMod p)ˣ
  XR : (ZMod p)ˣ
  conjugations : TreeLeafTuple Bool 2

noncomputable def rationalQuartetStates {p : ℕ} [Fact p.Prime] :
    (n : ℕ) → {C : (ZMod p)ˣ} → RationalTreeData (ZMod p)ˣ (n + 2) C →
      (ZMod p)ˣ → (ZMod p)ˣ → TreeLeafTuple Bool (n + 2) →
      TreeLeafTuple (ZMod p)ˣ n → Option (TreeLeafTuple (RationalQuartetState p) n)
  | 0, C, T, XL, XR, c, _ => some ⟨C, T, XL, XR, c⟩
  | n + 1, _, .node s CL CR u left right, XL, XR, c, P =>
    let HL := XL * CL * treeLeafProduct n P.1
    let HR := XR * CR * treeLeafProduct n P.2
    let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
    if hv : v = 0 then none else do
      let L ← rationalQuartetStates n left (Units.mk0 v hv) XL c.1 P.1
      let R ← rationalQuartetStates n right (Units.mk0 v hv) XR c.2 P.2
      pure (L, R)

def quartetCutValue {A B R : Type*} [Zero R] [Mul R] (f : A → B → R) (n : ℕ)
    (states : Option (TreeLeafTuple A n)) (b : TreeLeafTuple B n) : R :=
  match states with
  | none => 0
  | some a => treeLeafZipProduct f n a b

theorem quartetCutValue_pair {A B R : Type*} [MulZeroClass R] (f : A → B → R)
    (n : ℕ) (L R' : Option (TreeLeafTuple A n)) (b : TreeLeafTuple B (n + 1)) :
    quartetCutValue f (n + 1) (do let l ← L; let r ← R'; pure (l, r)) b =
      quartetCutValue f n L b.1 * quartetCutValue f n R' b.2 := by
  cases L <;> cases R' <;> simp [quartetCutValue, treeLeafZipProduct]

noncomputable def rationalQuartetStateAmplitude {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (S : RationalQuartetState p)
    (m : TreeLeafTuple (ZMod p)ˣ 2) : ℂ :=
  rationalTreeAmplitude g D S.tree S.XL S.XR S.conjugations m

/-- Holding all bottom-quartet products fixes the entire upper recursion. -/
theorem rationalTreeAmplitude_cut {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (m : TreeLeafTuple (ZMod p)ˣ (n + 2)) :
    rationalTreeAmplitude g D T XL XR c m =
      quartetCutValue (rationalQuartetStateAmplitude g D) n
        (rationalQuartetStates n T XL XR c
          (treeLeafMap (treeLeafProduct 2) n (quartetBlockTupleEquiv (ZMod p)ˣ n m)))
        (quartetBlockTupleEquiv (ZMod p)ˣ n m) := by
  induction n generalizing C XL XR with
  | zero => rfl
  | succ n ih =>
    cases T with
    | node s CL CR u left right =>
      change rationalTreeAmplitude g D (.node s CL CR u left right) XL XR c m =
        quartetCutValue (rationalQuartetStateAmplitude g D) (n + 1)
          (rationalQuartetStates (n + 1) (.node s CL CR u left right) XL XR c
            (treeLeafMap (treeLeafProduct 2) n (quartetBlockTupleEquiv (ZMod p)ˣ n m.1),
             treeLeafMap (treeLeafProduct 2) n (quartetBlockTupleEquiv (ZMod p)ˣ n m.2)))
          (quartetBlockTupleEquiv (ZMod p)ˣ n m.1, quartetBlockTupleEquiv (ZMod p)ˣ n m.2)
      simp only [rationalTreeAmplitude, rationalQuartetStates]
      simp only [treeLeafProduct_quartetBlocks n m.1, treeLeafProduct_quartetBlocks n m.2]
      split_ifs with hv
      · rfl
      · rw [quartetCutValue_pair]
        exact congrArg₂ (· * ·) (ih left _ _ c.1 m.1) (ih right _ _ c.2 m.2)

@[implicit_reducible] def treeLeafZip {A B : Type*} : (n : ℕ) → TreeLeafTuple A n → TreeLeafTuple B n →
    TreeLeafTuple (A × B) n
  | 0, a, b => (a, b)
  | n + 1, a, b => (treeLeafZip n a.1 b.1, treeLeafZip n a.2 b.2)

noncomputable def rationalQuartetStateArgument {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (S : RationalQuartetState p) (P : (ZMod p)ˣ) : (ZMod p)ˣ :=
  rationalTreeArgument S.tree.frequency S.C D S.XL S.XR P

/-- The weighted arguments exposed at the cut are exactly the leaves of
the truncated rational tree, with the same invalid-ancestor zeros. -/
theorem rationalQuartetStates_profile {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafTuple (ZMod p)ˣ n)
    (w : TreeLeafTuple (ZMod p → ℝ) n) :
    quartetCutValue (fun S (wp : (ZMod p → ℝ) × (ZMod p)ˣ) =>
        wp.1 (rationalQuartetStateArgument D S wp.2)) n
      (rationalQuartetStates n T XL XR c P) (treeLeafZip n w P) =
      rationalProfileLeafValue D (T.cutTwo n) w XL XR P := by
  induction n generalizing C XL XR with
  | zero => rfl
  | succ n ih =>
    cases T with
    | node s CL CR u left right =>
      simp only [rationalQuartetStates, RationalTreeData.cutTwo, rationalProfileLeafValue,
        RationalTreeData.frequency_cutTwo, treeLeafZip]
      split_ifs with hv
      · rfl
      · rw [quartetCutValue_pair]
        exact congrArg₂ (· * ·) (ih left _ _ c.1 P.1 w.1) (ih right _ _ c.2 P.2 w.2)

/-- Horizontal density domination applies directly to the genuine cut
states, even though their current entries depend on the product vector. -/
theorem rationalQuartetStates_profile_mean_le {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2))
    (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w) :
    (∑ P : TreeLeafTuple (ZMod p)ˣ n,
      quartetCutValue (fun S (wp : (ZMod p → ℝ) × (ZMod p)ˣ) =>
        wp.1 (rationalQuartetStateArgument D S wp.2)) n
        (rationalQuartetStates n T XL XR c P) (treeLeafZip n w P)) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤
        (2 : ℝ) ^ (2 ^ n - 1) * treeProfileMean n w := by
  simp_rw [rationalQuartetStates_profile]
  exact rationalProfileLeafValue_mean_le D (T.cutTwo n) w hw XL XR

end Ostmann

end OAI
