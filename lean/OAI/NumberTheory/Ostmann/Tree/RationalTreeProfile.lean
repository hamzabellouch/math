import OAI.NumberTheory.Ostmann.Characters.TreeProfile

namespace OAI

/-! # The actual rational tree with different weights at a horizontal level -/

namespace Ostmann

open scoped BigOperators

noncomputable def rationalProfileMoment {p : ℕ} [Fact p.Prime] (D : (ZMod p)ˣ) :
    {n : ℕ} → {C : (ZMod p)ˣ} → RationalTreeData (ZMod p)ˣ n C →
      TreeLeafTuple (ZMod p → ℝ) n → (ZMod p)ˣ → (ZMod p)ˣ → (ZMod p)ˣ → ℝ
  | _, _, .leaf s C, w, XL, XR, P => w (rationalTreeArgument s C D XL XR P)
  | _, _, .node s CL CR u left right, w, XL, XR, P =>
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ m : (ZMod p)ˣ,
      let HL : (ZMod p)ˣ := XL * CL * m
      let HR : (ZMod p)ˣ := XR * CR * (P / m)
      let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
      if hv : v = 0 then 0 else
        rationalProfileMoment D left w.1 (Units.mk0 v hv) XL m *
          rationalProfileMoment D right w.2 (Units.mk0 v hv) XR (P / m)

noncomputable def rationalProfileLeafValue {p : ℕ} [Fact p.Prime] (D : (ZMod p)ˣ) :
    {n : ℕ} → {C : (ZMod p)ˣ} → RationalTreeData (ZMod p)ˣ n C →
      TreeLeafTuple (ZMod p → ℝ) n → (ZMod p)ˣ → (ZMod p)ˣ →
        TreeLeafTuple (ZMod p)ˣ n → ℝ
  | _, _, .leaf s C, w, XL, XR, m => w (rationalTreeArgument s C D XL XR m)
  | n + 1, _, .node s CL CR u left right, w, XL, XR, ab =>
    let HL : (ZMod p)ˣ := XL * CL * treeLeafProduct n ab.1
    let HR : (ZMod p)ˣ := XR * CR * treeLeafProduct n ab.2
    let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
    if hv : v = 0 then 0 else
      rationalProfileLeafValue D left w.1 (Units.mk0 v hv) XL ab.1 *
        rationalProfileLeafValue D right w.2 (Units.mk0 v hv) XR ab.2

theorem rationalProfileMoment_nonneg {p : ℕ} [Fact p.Prime] (D : (ZMod p)ˣ)
    {n : ℕ} {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ n C)
    (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w)
    (XL XR P : (ZMod p)ˣ) : 0 ≤ rationalProfileMoment D T w XL XR P := by
  induction T generalizing XL XR P with
  | leaf s C => exact hw _
  | node s CL CR u left right ihL ihR =>
    simp only [rationalProfileMoment]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro m _
    dsimp
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (ihL w.1 hw.1 _ _ _) (ihR w.2 hw.2 _ _ _)

theorem rationalProfileMoment_le_majorant {p : ℕ} [Fact p.Prime] (D : (ZMod p)ˣ)
    {n : ℕ} {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ n C)
    (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w)
    (XL XR P : (ZMod p)ˣ) :
    rationalProfileMoment D T w XL XR P ≤
      treeProfileMajorant n w (rationalTreeArgument T.frequency C D XL XR P) := by
  induction T generalizing XL XR P with
  | leaf s C =>
    simp only [rationalProfileMoment, RationalTreeData.frequency, treeProfileMajorant,
      Units.ne_zero, ite_false, le_refl]
  | @node n s CL CR u left right ihL ihR =>
    have harg := rationalTreeArgument_node s CL CR D XL XR P
    change _ ≤ treeProfileMajorant (n + 1) w (rationalTreeArgument s (CL * CR) D XL XR P)
    rw [harg]
    simp only [treeProfileMajorant, Units.ne_zero, ite_false]
    calc
      _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          ∑ m : (ZMod p)ˣ, rationalNodeValue s left.frequency right.frequency D u XL XR CL CR P
            (treeProfileMajorant n w.1) (treeProfileMajorant n w.2) m := by
        unfold rationalProfileMoment
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro m _
        dsimp [rationalNodeValue]
        split_ifs with hv
        · exact le_rfl
        · have hL := ihL w.1 hw.1 (Units.mk0 _ hv) XL m
          have hR := ihR w.2 hw.2 (Units.mk0 _ hv) XR (P / m)
          rw [rationalTreeArgument_child] at hL hR
          exact mul_le_mul hL hR (rationalProfileMoment_nonneg D right w.2 hw.2 _ _ _)
            (treeProfileMajorant_nonneg n w.1 hw.1 _)
      _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          (2 * ∑ x : ZMod p, treeProfileMajorant n w.1 x *
            treeProfileMajorant n w.2 (x - rationalNodeArgument s D XL XR CL CR P)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact rationalNodeValue_sum_le s left.frequency right.frequency D u XL XR CL CR P
          _ _ (treeProfileMajorant_zero n w.1) (treeProfileMajorant_zero n w.2)
          (treeProfileMajorant_nonneg n w.1 hw.1) (treeProfileMajorant_nonneg n w.2 hw.2)
      _ = _ := by unfold differenceMoment; ring

theorem rationalProfileMoment_mean_le {p : ℕ} [Fact p.Prime] (D : (ZMod p)ˣ)
    {n : ℕ} {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ n C)
    (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w)
    (XL XR : (ZMod p)ˣ) :
    (∑ P : (ZMod p)ˣ, rationalProfileMoment D T w XL XR P) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ (2 : ℝ) ^ (2 ^ n - 1) * treeProfileMean n w := by
  calc
    _ ≤ (∑ P : (ZMod p)ˣ,
        treeProfileMajorant n w (rationalTreeArgument T.frequency C D XL XR P)) /
          (Fintype.card (ZMod p)ˣ : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun P _ => rationalProfileMoment_le_majorant D T w hw XL XR P
    _ = (∑ d : (ZMod p)ˣ, treeProfileMajorant n w d) /
          (Fintype.card (ZMod p)ˣ : ℝ) := by
      congr 1
      exact (rationalTreeArgumentEquiv T.frequency C D XL XR).sum_comp
        (fun d => treeProfileMajorant n w d)
    _ ≤ _ := treeProfileMajorant_mean_le n w hw

end Ostmann

end OAI
