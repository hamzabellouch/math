import OAI.NumberTheory.Ostmann.Tree.RationalTreeProfile

namespace OAI

/-! # Weighted horizontal-level averages with actual independent leaf products -/

namespace Ostmann

open scoped BigOperators

theorem rationalProfileLeafValue_fiber_sum {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C)
    (w : TreeLeafTuple (ZMod p → ℝ) n) (XL XR P : (ZMod p)ˣ) :
    (∑ x : TreeLeafFiber (ZMod p)ˣ n P, rationalProfileLeafValue D T w XL XR x.1) =
      (Fintype.card (ZMod p)ˣ : ℝ) ^ (2 ^ n - 1) * rationalProfileMoment D T w XL XR P := by
  induction T generalizing XL XR P with
  | leaf s C =>
    have he : ∀ x : TreeLeafFiber (ZMod p)ˣ 0 P, (x.1 : (ZMod p)ˣ) = P :=
      fun x => x.property
    simp only [rationalProfileLeafValue, he, Finset.sum_const, Finset.card_univ,
      card_treeLeafFiber, pow_zero, Nat.sub_self, pow_zero, one_smul, one_mul,
      rationalProfileMoment]
  | @node n s CL CR u left right ihL ihR =>
    rw [sum_treeLeafFiber_succ]
    have hterm (m : (ZMod p)ˣ) :
        (∑ a : TreeLeafFiber (ZMod p)ˣ n m,
          ∑ b : TreeLeafFiber (ZMod p)ˣ n (P / m),
            rationalProfileLeafValue D (.node s CL CR u left right) w XL XR (a.1, b.1)) =
        ((Fintype.card (ZMod p)ˣ : ℝ) ^ (2 ^ n - 1)) ^ 2 *
          (let HL : (ZMod p)ˣ := XL * CL * m
           let HR : (ZMod p)ˣ := XR * CR * (P / m)
           let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
           if hv : v = 0 then 0 else
             rationalProfileMoment D left w.1 (Units.mk0 v hv) XL m *
               rationalProfileMoment D right w.2 (Units.mk0 v hv) XR (P / m)) := by
      have hfib {Q : (ZMod p)ˣ} (x : TreeLeafFiber (ZMod p)ˣ n Q) :
          treeLeafProduct n x.1 = Q := x.property
      simp only [rationalProfileLeafValue, hfib]
      dsimp
      split_ifs with hv
      · simp
      · let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u
          ((XL : ZMod p) * CL * m) ((XR : ZMod p) * CR * (P / m : (ZMod p)ˣ))
        let V : (ZMod p)ˣ := Units.mk0 v hv
        change (∑ a : TreeLeafFiber (ZMod p)ˣ n m,
          ∑ b : TreeLeafFiber (ZMod p)ˣ n (P / m),
            rationalProfileLeafValue D left w.1 V XL a.1 *
            rationalProfileLeafValue D right w.2 V XR b.1) = _
        rw [← Fintype.sum_mul_sum
          (fun a : TreeLeafFiber (ZMod p)ˣ n m => rationalProfileLeafValue D left w.1 V XL a.1)
          (fun b : TreeLeafFiber (ZMod p)ˣ n (P / m) => rationalProfileLeafValue D right w.2 V XR b.1)]
        rw [ihL, ihR]
        ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    simp only [rationalProfileMoment]
    have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    have hexp : 2 ^ (n + 1) - 1 = (2 ^ n - 1) * 2 + 1 := by
      rw [pow_succ]
      omega
    rw [hexp]
    conv_rhs => arg 1; rw [pow_succ, pow_mul]
    field_simp

theorem rationalProfileLeafValue_mean_eq {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C)
    (w : TreeLeafTuple (ZMod p → ℝ) n) (XL XR : (ZMod p)ˣ) :
    (∑ x : TreeLeafTuple (ZMod p)ˣ n, rationalProfileLeafValue D T w XL XR x) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) =
    (∑ P : (ZMod p)ˣ, rationalProfileMoment D T w XL XR P) /
      (Fintype.card (ZMod p)ˣ : ℝ) := by
  rw [sum_treeLeafTuple_by_product]
  simp_rw [rationalProfileLeafValue_fiber_sum]
  rw [← Finset.mul_sum, card_treeLeafTuple, Nat.cast_pow]
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  conv_lhs => rhs; rw [← Nat.sub_add_cancel hn, pow_succ]
  field_simp

/-- Horizontal-level domination for a different nonnegative test at each node. -/
theorem rationalProfileLeafValue_mean_le {p : ℕ} [Fact p.Prime] (D : (ZMod p)ˣ)
    {n : ℕ} {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ n C)
    (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w)
    (XL XR : (ZMod p)ˣ) :
    (∑ x : TreeLeafTuple (ZMod p)ˣ n, rationalProfileLeafValue D T w XL XR x) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤
        (2 : ℝ) ^ (2 ^ n - 1) * treeProfileMean n w := by
  rw [rationalProfileLeafValue_mean_eq]
  exact rationalProfileMoment_mean_le D T w hw XL XR

end Ostmann

end OAI
