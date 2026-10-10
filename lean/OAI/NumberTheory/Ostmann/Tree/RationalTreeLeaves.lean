import OAI.NumberTheory.Ostmann.Tree.RationalTree
import OAI.NumberTheory.Ostmann.Characters.TreeLeafProducts

namespace OAI

/-! # The rational tree under independent uniform leaf sampling -/

namespace Ostmann

open scoped BigOperators

noncomputable def rationalTreeLeafValue {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (D : (ZMod p)ˣ) :
    {n : ℕ} → {C : (ZMod p)ˣ} → RationalTreeData (ZMod p)ˣ n C →
      (ZMod p)ˣ → (ZMod p)ˣ → TreeLeafTuple (ZMod p)ˣ n → ℝ
  | _, _, .leaf s C, XL, XR, m => w (rationalTreeArgument s C D XL XR m)
  | n + 1, _, .node s CL CR u left right, XL, XR, ab =>
    let HL : (ZMod p)ˣ := XL * CL * treeLeafProduct n ab.1
    let HR : (ZMod p)ˣ := XR * CR * treeLeafProduct n ab.2
    let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
    if hv : v = 0 then 0 else
      rationalTreeLeafValue w D left (Units.mk0 v hv) XL ab.1 *
        rationalTreeLeafValue w D right (Units.mk0 v hv) XR ab.2

theorem rationalTreeLeafValue_fiber_sum {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR P : (ZMod p)ˣ) :
    (∑ x : TreeLeafFiber (ZMod p)ˣ n P, rationalTreeLeafValue w D T XL XR x.1) =
      (Fintype.card (ZMod p)ˣ : ℝ) ^ (2 ^ n - 1) * rationalTreeMoment w D T XL XR P := by
  induction T generalizing XL XR P with
  | leaf s C =>
    have he : ∀ x : TreeLeafFiber (ZMod p)ˣ 0 P, (x.1 : (ZMod p)ˣ) = P :=
      fun x => x.property
    simp only [rationalTreeLeafValue, he, Finset.sum_const, Finset.card_univ,
      card_treeLeafFiber, pow_zero, Nat.sub_self, pow_zero, one_smul, one_mul,
      rationalTreeMoment]
  | @node n s CL CR u left right ihL ihR =>
    rw [sum_treeLeafFiber_succ]
    have hterm (m : (ZMod p)ˣ) :
        (∑ a : TreeLeafFiber (ZMod p)ˣ n m,
          ∑ b : TreeLeafFiber (ZMod p)ˣ n (P / m),
            rationalTreeLeafValue w D (.node s CL CR u left right) XL XR (a.1, b.1)) =
        ((Fintype.card (ZMod p)ˣ : ℝ) ^ (2 ^ n - 1)) ^ 2 *
          (let HL : (ZMod p)ˣ := XL * CL * m
           let HR : (ZMod p)ˣ := XR * CR * (P / m)
           let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
           if hv : v = 0 then 0 else
             rationalTreeMoment w D left (Units.mk0 v hv) XL m *
               rationalTreeMoment w D right (Units.mk0 v hv) XR (P / m)) := by
      have hfib {Q : (ZMod p)ˣ} (x : TreeLeafFiber (ZMod p)ˣ n Q) :
          treeLeafProduct n x.1 = Q := x.property
      simp only [rationalTreeLeafValue, hfib]
      dsimp
      split_ifs with hv
      · simp
      · let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u
          ((XL : ZMod p) * CL * m) ((XR : ZMod p) * CR * (P / m : (ZMod p)ˣ))
        let V : (ZMod p)ˣ := Units.mk0 v hv
        change (∑ a : TreeLeafFiber (ZMod p)ˣ n m,
          ∑ b : TreeLeafFiber (ZMod p)ˣ n (P / m),
            rationalTreeLeafValue w D left V XL a.1 *
            rationalTreeLeafValue w D right V XR b.1) = _
        rw [← Fintype.sum_mul_sum
          (fun a : TreeLeafFiber (ZMod p)ˣ n m => rationalTreeLeafValue w D left V XL a.1)
          (fun b : TreeLeafFiber (ZMod p)ˣ n (P / m) => rationalTreeLeafValue w D right V XR b.1)]
        rw [ihL, ihR]
        ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    simp only [rationalTreeMoment]
    have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    have hexp : 2 ^ (n + 1) - 1 = (2 ^ n - 1) * 2 + 1 := by
      rw [pow_succ]
      omega
    rw [hexp]
    conv_rhs => arg 1; rw [pow_succ, pow_mul]
    field_simp

theorem rationalTreeLeafValue_mean_eq {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ) :
    (∑ x : TreeLeafTuple (ZMod p)ˣ n, rationalTreeLeafValue w D T XL XR x) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) =
    (∑ P : (ZMod p)ˣ, rationalTreeMoment w D T XL XR P) /
      (Fintype.card (ZMod p)ˣ : ℝ) := by
  rw [sum_treeLeafTuple_by_product]
  simp_rw [rationalTreeLeafValue_fiber_sum]
  rw [← Finset.mul_sum, card_treeLeafTuple, Nat.cast_pow]
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  conv_lhs => rhs; rw [← Nat.sub_add_cancel hn, pow_succ]
  field_simp

/-- The first part of the tree comparison: independent uniform leaves give the `3^r` bound. -/
theorem rationalTreeLeafValue_l2_bound {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ) :
    (∑ x : TreeLeafTuple (ZMod p)ˣ n,
      rationalTreeLeafValue (fun y => ‖g y‖ ^ 2) D T XL XR x) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  rw [rationalTreeLeafValue_mean_eq]
  exact rationalTreeMoment_l2_bound hp g hg henergy D T XL XR

/-- The manuscript's diagram value, permitting arbitrary conjugation choices at the leaves. -/
noncomputable def rationalTreeAmplitude {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) :
    {n : ℕ} → {C : (ZMod p)ˣ} → RationalTreeData (ZMod p)ˣ n C →
      (ZMod p)ˣ → (ZMod p)ˣ → TreeLeafTuple Bool n → TreeLeafTuple (ZMod p)ˣ n → ℂ
  | _, _, .leaf s C, XL, XR, c, m =>
    match (c : Bool) with
    | true => star (g (rationalTreeArgument s C D XL XR m))
    | false => g (rationalTreeArgument s C D XL XR m)
  | n + 1, _, .node s CL CR u left right, XL, XR, c, ab =>
    let HL : (ZMod p)ˣ := XL * CL * treeLeafProduct n ab.1
    let HR : (ZMod p)ˣ := XR * CR * treeLeafProduct n ab.2
    let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
    if hv : v = 0 then 0 else
      rationalTreeAmplitude g D left (Units.mk0 v hv) XL c.1 ab.1 *
        rationalTreeAmplitude g D right (Units.mk0 v hv) XR c.2 ab.2

theorem norm_rationalTreeAmplitude_sq {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool n) (m : TreeLeafTuple (ZMod p)ˣ n) :
    ‖rationalTreeAmplitude g D T XL XR c m‖ ^ 2 =
      rationalTreeLeafValue (fun y => ‖g y‖ ^ 2) D T XL XR m := by
  induction T generalizing XL XR with
  | leaf s C =>
    cases c <;> simp [rationalTreeAmplitude, rationalTreeLeafValue]
  | node s CL CR u left right ihL ihR =>
    simp only [rationalTreeAmplitude, rationalTreeLeafValue]
    split_ifs
    · simp
    · rw [norm_mul, mul_pow, ihL, ihR]

/-- Equation `src37`, with the actual reconstructed-node diagram and uniform independent leaves. -/
theorem rationalTreeAmplitude_l2_bound {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool n) :
    (∑ m : TreeLeafTuple (ZMod p)ˣ n, ‖rationalTreeAmplitude g D T XL XR c m‖ ^ 2) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  simp_rw [norm_rationalTreeAmplitude_sq]
  exact rationalTreeLeafValue_l2_bound hp g hg henergy D T XL XR

end Ostmann

end OAI
