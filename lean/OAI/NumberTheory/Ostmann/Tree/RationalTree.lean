import OAI.NumberTheory.Ostmann.ZeroDensity.RationalNodeDensity
import OAI.NumberTheory.Ostmann.ZeroDensity.TreeDensity

namespace OAI

/-!
# Recursive rational tree data

The product coefficient is an index of the data type. At every split,
its child indices encode exactly the consistency conditions on the
fixed constants in `src36`.
-/

namespace Ostmann

open scoped BigOperators

inductive RationalTreeData (U : Type*) [CommGroup U] : ℕ → U → Type _
  | leaf (s C : U) : RationalTreeData U 0 C
  | node {n : ℕ} (s CL CR u : U)
      (left : RationalTreeData U n (u * CL))
      (right : RationalTreeData U n (u * CR)) : RationalTreeData U (n + 1) (CL * CR)

@[implicit_reducible] def RationalTreeData.frequency {U : Type*} [CommGroup U] {n : ℕ} {C : U} :
    RationalTreeData U n C → U
  | .leaf s _ => s
  | .node s _ _ _ _ _ => s

noncomputable def rationalTreeArgument {p : ℕ} [Fact p.Prime]
    (s C D XL XR P : (ZMod p)ˣ) : (ZMod p)ˣ := s / (D * XL * XR * C * P)

noncomputable def rationalTreeMoment {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (D : (ZMod p)ˣ) :
    {n : ℕ} → {C : (ZMod p)ˣ} → RationalTreeData (ZMod p)ˣ n C →
      (ZMod p)ˣ → (ZMod p)ˣ → (ZMod p)ˣ → ℝ
  | _, _, .leaf s C, XL, XR, P => w (rationalTreeArgument s C D XL XR P)
  | _, _, .node s CL CR u left right, XL, XR, P =>
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ m : (ZMod p)ˣ,
      let HL : (ZMod p)ˣ := XL * CL * m
      let HR : (ZMod p)ˣ := XR * CR * (P / m)
      let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
      if hv : v = 0 then 0 else
        rationalTreeMoment w D left (Units.mk0 v hv) XL m *
          rationalTreeMoment w D right (Units.mk0 v hv) XR (P / m)

theorem rationalTreeArgument_child {p : ℕ} [Fact p.Prime]
    (s D u X C m v : (ZMod p)ˣ) :
    (rationalTreeArgument s (u * C) D v X m : ZMod p) =
      childArgument (s : ZMod p) D u ((X * C * m : (ZMod p)ˣ) : ZMod p) v := by
  simp only [rationalTreeArgument, childArgument, Units.val_div_eq_div_val, Units.val_mul]
  congr 1
  ring

theorem rationalTreeArgument_node {p : ℕ} [Fact p.Prime]
    (s CL CR D XL XR P : (ZMod p)ˣ) :
    rationalTreeArgument s (CL * CR) D XL XR P = rationalNodeArgument s D XL XR CL CR P := by
  unfold rationalTreeArgument rationalNodeArgument
  congr 1
  simp only [mul_left_comm, mul_comm]

theorem rationalTreeMoment_nonneg {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (D : (ZMod p)ˣ)
    {n : ℕ} {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ n C)
    (XL XR P : (ZMod p)ˣ) : 0 ≤ rationalTreeMoment w D T XL XR P := by
  induction T generalizing XL XR P with
  | leaf s C => exact hw _
  | node s CL CR u left right ihL ihR =>
    simp only [rationalTreeMoment]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro m _
    dsimp
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (ihL _ _ _) (ihR _ _ _)

/-- The actual recursive rational-node moment is bounded by the uniform density majorant. -/
theorem rationalTreeMoment_le_majorant {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (D : (ZMod p)ˣ)
    {n : ℕ} {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ n C)
    (XL XR P : (ZMod p)ˣ) :
    rationalTreeMoment w D T XL XR P ≤
      treeDensityMajorant w n (rationalTreeArgument T.frequency C D XL XR P) := by
  induction T generalizing XL XR P with
  | leaf s C =>
    simp only [rationalTreeMoment, RationalTreeData.frequency, treeDensityMajorant,
      Units.ne_zero, ite_false, le_refl]
  | @node n s CL CR u left right ihL ihR =>
    have harg := rationalTreeArgument_node s CL CR D XL XR P
    change _ ≤ treeDensityMajorant w (n + 1) (rationalTreeArgument s (CL * CR) D XL XR P)
    rw [harg]
    simp only [treeDensityMajorant, Units.ne_zero, ite_false]
    calc
      _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          ∑ m : (ZMod p)ˣ, rationalNodeValue s left.frequency right.frequency D u XL XR CL CR P
            (treeDensityMajorant w n) (treeDensityMajorant w n) m := by
        unfold rationalTreeMoment
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro m _
        dsimp [rationalNodeValue]
        split_ifs with hv
        · exact le_rfl
        · have hL := ihL (Units.mk0 _ hv) XL m
          have hR := ihR (Units.mk0 _ hv) XR (P / m)
          rw [rationalTreeArgument_child] at hL hR
          exact mul_le_mul hL hR (rationalTreeMoment_nonneg w hw D right _ _ _)
            (treeDensityMajorant_nonneg w hw n _)
      _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          (2 * ∑ x : ZMod p, treeDensityMajorant w n x *
            treeDensityMajorant w n (x - rationalNodeArgument s D XL XR CL CR P)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact rationalNodeValue_sum_le s left.frequency right.frequency D u XL XR CL CR P
          _ _ (treeDensityMajorant_zero w n) (treeDensityMajorant_zero w n)
          (treeDensityMajorant_nonneg w hw n) (treeDensityMajorant_nonneg w hw n)
      _ = _ := by unfold differenceMoment; ring

/-- With the other root data fixed, exposing the total leaf product gives a uniform argument. -/
noncomputable def rationalTreeArgumentEquiv {p : ℕ} [Fact p.Prime]
    (s C D XL XR : (ZMod p)ˣ) : (ZMod p)ˣ ≃ (ZMod p)ˣ where
  toFun P := rationalTreeArgument s C D XL XR P
  invFun y := s / (D * XL * XR * C * y)
  left_inv P := by simp [rationalTreeArgument, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  right_inv y := by simp [rationalTreeArgument, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

theorem rationalTreeMoment_mean_le {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (E : ℝ)
    (hE : (∑ d : (ZMod p)ˣ, w d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ E)
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ) :
    (∑ P : (ZMod p)ˣ, rationalTreeMoment w D T XL XR P) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ binaryMomentBound E n := by
  calc
    _ ≤ (∑ P : (ZMod p)ˣ,
        treeDensityMajorant w n (rationalTreeArgument T.frequency C D XL XR P)) /
          (Fintype.card (ZMod p)ˣ : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun P _ => rationalTreeMoment_le_majorant w hw D T XL XR P
    _ = (∑ d : (ZMod p)ˣ, treeDensityMajorant w n d) /
          (Fintype.card (ZMod p)ˣ : ℝ) := by
      congr 1
      exact (rationalTreeArgumentEquiv T.frequency C D XL XR).sum_comp
        (fun d => treeDensityMajorant w n d)
    _ ≤ _ := treeDensityMajorant_mean_le w hw E hE n

/-- The actual rational tree, averaged in its root product, satisfies `src37`. -/
theorem rationalTreeMoment_l2_bound {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ) :
    (∑ P : (ZMod p)ˣ, rationalTreeMoment (fun x => ‖g x‖ ^ 2) D T XL XR P) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  have hpr : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  have hsum := sum_units_eq_sum_of_zero (fun x => ‖g x‖ ^ 2) (by simp [hg])
  have hE : (∑ d : (ZMod p)ˣ, ‖g d‖ ^ 2) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ 3 / 2 := by
    rw [hU, hsum]
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < p - 1)).mpr
    linarith
  have h := rationalTreeMoment_mean_le (fun x => ‖g x‖ ^ 2) (fun _ => sq_nonneg _)
    (3 / 2) hE D T XL XR
  rw [binaryMomentBound_eq] at h
  norm_num only [show (2 : ℝ) * (3 / 2) = 3 by norm_num] at h
  exact h.trans (by have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (2 ^ n); linarith)

end Ostmann

end OAI
