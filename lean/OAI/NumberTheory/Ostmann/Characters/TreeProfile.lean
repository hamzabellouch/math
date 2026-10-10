import OAI.NumberTheory.Ostmann.Tree.RationalTreeLeaves

namespace OAI

/-! # Nonuniform nonnegative weights at a horizontal level of the tree -/

namespace Ostmann

open scoped BigOperators

def treeWeightsNonneg {p : ℕ} : (n : ℕ) → TreeLeafTuple (ZMod p → ℝ) n → Prop
  | 0, w => ∀ x, 0 ≤ w x
  | n + 1, w => treeWeightsNonneg n w.1 ∧ treeWeightsNonneg n w.2

noncomputable def treeProfileMean {p : ℕ} [Fact p.Prime] :
    (n : ℕ) → TreeLeafTuple (ZMod p → ℝ) n → ℝ
  | 0, w => (∑ x : (ZMod p)ˣ, w x) / (Fintype.card (ZMod p)ˣ : ℝ)
  | n + 1, w => treeProfileMean n w.1 * treeProfileMean n w.2

noncomputable def treeProfileMajorant {p : ℕ} [Fact p.Prime] :
    (n : ℕ) → TreeLeafTuple (ZMod p → ℝ) n → ZMod p → ℝ
  | 0, w, d => if d = 0 then 0 else w d
  | n + 1, w, d => if d = 0 then 0 else
      (2 / (Fintype.card (ZMod p)ˣ : ℝ)) *
        differenceMoment (treeProfileMajorant n w.1) (treeProfileMajorant n w.2) d

theorem treeProfileMajorant_zero {p : ℕ} [Fact p.Prime]
    (n : ℕ) (w : TreeLeafTuple (ZMod p → ℝ) n) : treeProfileMajorant n w 0 = 0 := by
  cases n <;> simp [treeProfileMajorant]

theorem treeProfileMajorant_nonneg {p : ℕ} [Fact p.Prime]
    (n : ℕ) (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w)
    (d : ZMod p) : 0 ≤ treeProfileMajorant n w d := by
  induction n generalizing d with
  | zero =>
    simp only [treeProfileMajorant]
    split_ifs
    · exact le_rfl
    · exact hw d
  | succ n ih =>
    simp only [treeProfileMajorant]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by positivity)
        (differenceMoment_nonneg _ _ (ih w.1 hw.1) (ih w.2 hw.2) d)

theorem treeProfileMean_nonneg {p : ℕ} [Fact p.Prime]
    (n : ℕ) (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w) :
    0 ≤ treeProfileMean n w := by
  induction n with
  | zero => exact div_nonneg (Finset.sum_nonneg fun x _ => hw x) (Nat.cast_nonneg _)
  | succ n ih => exact mul_nonneg (ih w.1 hw.1) (ih w.2 hw.2)

/-- The density loss is two for every internal node, with a separate mean for each leaf. -/
theorem treeProfileMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (n : ℕ) (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w) :
    (∑ d : (ZMod p)ˣ, treeProfileMajorant n w d) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤
        (2 : ℝ) ^ (2 ^ n - 1) * treeProfileMean n w := by
  induction n with
  | zero => simp [treeProfileMajorant, treeProfileMean, Units.ne_zero]
  | succ n ih =>
    have hU : 0 < (Fintype.card (ZMod p)ˣ : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hL := ih w.1 hw.1
    have hR := ih w.2 hw.2
    have hzL := sum_units_eq_sum_of_zero _ (treeProfileMajorant_zero n w.1)
    have hzR := sum_units_eq_sum_of_zero _ (treeProfileMajorant_zero n w.2)
    have hnL : 0 ≤ (∑ d : (ZMod p)ˣ, treeProfileMajorant n w.1 d) /
        (Fintype.card (ZMod p)ˣ : ℝ) :=
      div_nonneg (Finset.sum_nonneg fun d _ => treeProfileMajorant_nonneg n w.1 hw.1 d) hU.le
    have hnR : 0 ≤ (2 : ℝ) ^ (2 ^ n - 1) * treeProfileMean n w.2 :=
      mul_nonneg (by positivity) (treeProfileMean_nonneg n w.2 hw.2)
    calc
      _ = (2 / (Fintype.card (ZMod p)ˣ : ℝ)) *
          (∑ d : (ZMod p)ˣ,
            differenceMoment (treeProfileMajorant n w.1) (treeProfileMajorant n w.2) d) /
              (Fintype.card (ZMod p)ˣ : ℝ) := by
        simp only [treeProfileMajorant, Units.ne_zero, ite_false, ← Finset.mul_sum]
      _ ≤ (2 / (Fintype.card (ZMod p)ˣ : ℝ)) *
          ((∑ x : ZMod p, treeProfileMajorant n w.1 x) *
            ∑ x : ZMod p, treeProfileMajorant n w.2 x) /
              (Fintype.card (ZMod p)ˣ : ℝ) := by
        apply div_le_div_of_nonneg_right _ hU.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_units_differenceMoment_le _ _
          (treeProfileMajorant_nonneg n w.1 hw.1) (treeProfileMajorant_nonneg n w.2 hw.2)
      _ = 2 * (((∑ d : (ZMod p)ˣ, treeProfileMajorant n w.1 d) /
          (Fintype.card (ZMod p)ˣ : ℝ)) *
          ((∑ d : (ZMod p)ˣ, treeProfileMajorant n w.2 d) /
          (Fintype.card (ZMod p)ˣ : ℝ))) := by rw [← hzL, ← hzR]; ring
      _ ≤ 2 * (((2 : ℝ) ^ (2 ^ n - 1) * treeProfileMean n w.1) *
          ((2 : ℝ) ^ (2 ^ n - 1) * treeProfileMean n w.2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hL hR
          (div_nonneg (Finset.sum_nonneg fun d _ =>
            treeProfileMajorant_nonneg n w.2 hw.2 d) hU.le)
          (mul_nonneg (by positivity) (treeProfileMean_nonneg n w.1 hw.1))) (by norm_num)
      _ = _ := by
        have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
        have he : 2 ^ (n + 1) - 1 = (2 ^ n - 1) + (2 ^ n - 1) + 1 := by
          rw [pow_succ]; omega
        rw [he, pow_add, pow_add]
        simp only [treeProfileMean, pow_one]
        ring

end Ostmann

end OAI
