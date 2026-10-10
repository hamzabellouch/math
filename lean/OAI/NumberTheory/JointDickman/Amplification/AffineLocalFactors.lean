import OAI.NumberTheory.JointDickman.Arithmetic.AffineRectangleSieve

namespace OAI

/-! # Exact local means for the three forms b, c, b+jc -/

namespace JointDickman

open Finset

open Classical in
noncomputable def residueWeight {α : Type*} (t : ℝ) (a x : α) : ℝ :=
  if x = a then t else 1

open Classical in
theorem sum_residueWeight {α : Type*} [Fintype α] (t : ℝ) (a : α) :
    ∑ x : α, residueWeight t a x = (Fintype.card α : ℝ) - 1 + t := by
  have heq (x : α) : residueWeight t a x = 1 + (if x = a then t - 1 else 0) := by
    by_cases h : x = a <;> simp [residueWeight, h]
  simp_rw [heq]
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_eq', mem_univ, ite_true]
  ring

open Classical in
theorem sum_two_residueWeights {α : Type*} [Fintype α] (t u : ℝ) (a b : α)
    (hab : a ≠ b) :
    ∑ x : α, residueWeight t a x * residueWeight u b x =
      (Fintype.card α : ℝ) - 2 + t + u := by
  have heq (x : α) : residueWeight t a x * residueWeight u b x =
      1 + (if x = a then t - 1 else 0) + (if x = b then u - 1 else 0) := by
    by_cases ha : x = a <;> by_cases hb : x = b
    · exact False.elim (hab (ha.symm.trans hb))
    all_goals simp [residueWeight, ha, hb, hab, Ne.symm hab]
  simp_rw [heq]
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_eq', mem_univ, ite_true]
  ring

open Classical in
theorem sum_squared_residueWeight {α : Type*} [Fintype α] (t : ℝ) (a : α) :
    ∑ x : α, residueWeight t a x ^ 2 = (Fintype.card α : ℝ) - 1 + t ^ 2 := by
  have heq (x : α) : residueWeight t a x ^ 2 = residueWeight (t ^ 2) a x := by
    by_cases h : x = a <;> simp [residueWeight, h]
  simp_rw [heq]
  exact sum_residueWeight _ _

open Classical in
theorem three_affine_residue_sum {p : ℕ} [Fact p.Prime]
    (j : ZMod p) (hj : j ≠ 0) (t : ℝ) :
    (∑ b : ZMod p, ∑ c : ZMod p,
      residueWeight t 0 b * residueWeight t 0 c * residueWeight t 0 (b + j * c)) =
      t * ((p : ℝ) - 1 + t ^ 2) + ((p : ℝ) - 1) * ((p : ℝ) - 2 + 2 * t) := by
  rw [sum_comm]
  have hinner (c : ZMod p) : (∑ b : ZMod p,
      residueWeight t 0 b * residueWeight t 0 c * residueWeight t 0 (b + j * c)) =
      if c = 0 then t * ((p : ℝ) - 1 + t ^ 2) else (p : ℝ) - 2 + 2 * t := by
    by_cases hc : c = 0
    · subst c
      simp only [mul_zero, add_zero, residueWeight, ite_true]
      have hs := sum_squared_residueWeight t (0 : ZMod p)
      simp only [ZMod.card] at hs
      calc
        _ = t * ∑ b : ZMod p, residueWeight t 0 b ^ 2 := by
          rw [mul_sum]
          apply sum_congr rfl
          intro b _
          by_cases hb : b = 0
          · simp [residueWeight, hb]
            ring
          · simp [residueWeight, hb]
        _ = _ := by rw [hs]
    · have hroot : (0 : ZMod p) ≠ -(j * c) := by
        intro h
        have : j * c = 0 := neg_eq_zero.mp h.symm
        exact (mul_ne_zero hj hc) this
      have heq (b : ZMod p) : residueWeight t 0 (b + j * c) = residueWeight t (-(j * c)) b := by
        simp [residueWeight, add_eq_zero_iff_eq_neg]
      simp only [hc, residueWeight, ite_false, mul_one]
      change (∑ b : ZMod p, residueWeight t 0 b * residueWeight t 0 (b + j * c)) = _
      simp_rw [heq]
      simpa only [ZMod.card, two_mul, add_assoc] using
        sum_two_residueWeights t t (0 : ZMod p) (-(j * c)) hroot
  simp_rw [hinner]
  have heq (c : ZMod p) :
      (if c = 0 then t * ((p : ℝ) - 1 + t ^ 2) else (p : ℝ) - 2 + 2 * t) =
      ((p : ℝ) - 2 + 2 * t) +
        (if c = 0 then t * ((p : ℝ) - 1 + t ^ 2) - ((p : ℝ) - 2 + 2 * t) else 0) := by
    by_cases hc : c = 0 <;> simp [hc]
  simp_rw [heq]
  simp only [sum_add_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, sum_ite_eq', mem_univ,
    ite_true]
  ring

open Classical in
theorem three_affine_residue_sum_degenerate {p : ℕ} [NeZero p] (t : ℝ) :
    (∑ b : ZMod p, ∑ c : ZMod p,
      residueWeight t 0 b * residueWeight t 0 c * residueWeight t 0 b) =
      ((p : ℝ) - 1 + t ^ 2) * ((p : ℝ) - 1 + t) := by
  have heq (b c : ZMod p) : residueWeight t 0 b * residueWeight t 0 c * residueWeight t 0 b =
      residueWeight t 0 b ^ 2 * residueWeight t 0 c := by ring
  simp_rw [heq, ← mul_sum]
  rw [← sum_mul, sum_squared_residueWeight, sum_residueWeight, ZMod.card]

end JointDickman

end OAI
