import OAI.NumberTheory.Ostmann.Arithmetic.BulkWeightedErrorBudget
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # The full bulk cell and residue count fits the progression budget -/

namespace Ostmann
open scoped Classical BigOperators

theorem bulk_weighted_cost_le_exp {J Cell : Type*} [Fintype J] [Fintype Cell]
    (M : ℕ) [NeZero M] (Z : J → ℝ) (A B C L : ℝ)
    (hC : 1 ≤ C) (hL : 1 ≤ L) (hZ0 : ∀ j, 0 ≤ Z j) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hJ : (Fintype.card J : ℝ) ≤ C * L) (hZ : ∀ j, Z j ≤ Real.exp (C * L))
    (hcell : (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)))
    (hunit : (Fintype.card (ZMod M)ˣ : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L)))
    (hA : A ≤ Real.exp (C * L * Real.exp ((1 / 1000 : ℝ) * L)))
    (hB : B ≤ Real.exp (C * L ^ 2)) :
    (∏ j, Z j) * (Fintype.card Cell : ℝ) ^ Fintype.card J *
        (Fintype.card (ZMod M)ˣ : ℝ) ^ Fintype.card J * A *
        2 ^ Fintype.card J * (Fintype.card J : ℝ) * B ≤
      Real.exp (8 * C ^ 2 * L ^ 2 + 8 * C ^ 2 * L * Real.exp ((14 / 10000 : ℝ) * L)) := by
  have hC0 : 0 ≤ C := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hCL : 0 ≤ C * L := mul_nonneg hC0 hL0
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hCeq : C ≤ C ^ 2 := by nlinarith
  have hbig : Real.exp ((12 / 10000 : ℝ) * L) ≤ Real.exp ((14 / 10000 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hsmall : Real.exp ((1 / 1000 : ℝ) * L) ≤ Real.exp ((14 / 10000 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hz : (∏ j, Z j) ≤ Real.exp (C ^ 2 * L ^ 2) := by
    calc
      _ ≤ ∏ _j : J, Real.exp (C * L) := Finset.prod_le_prod₀ (fun j _ => hZ0 j) (fun j _ => hZ j)
      _ = Real.exp ((Fintype.card J : ℝ) * (C * L)) := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hJ hCL])
  have hp (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L))) :
      x ^ Fintype.card J ≤ Real.exp (C * L * Real.exp ((14 / 10000 : ℝ) * L)) := by
    apply (pow_le_pow_left₀ hx0 hx _).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hJ (Real.exp_nonneg _))
  have hc := hp _ (Nat.cast_nonneg _) hcell
  have hu := hp _ (Nat.cast_nonneg _) (hunit.trans (Real.exp_le_exp.mpr hbig))
  have ha : A ≤ Real.exp (C * L * Real.exp ((14 / 10000 : ℝ) * L)) :=
    hA.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsmall hCL))
  have htwo : (2 : ℝ) ^ Fintype.card J ≤ Real.exp (C * L ^ 2) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    apply (pow_le_pow_left₀ (by norm_num) he _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hLsq hC0]
  have hj : (Fintype.card J : ℝ) ≤ Real.exp (C * L ^ 2) := by
    apply hJ.trans
    have he := Real.add_one_le_exp (C * L)
    exact (by linarith : C * L ≤ Real.exp (C * L)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLsq hC0))
  calc
    _ ≤ Real.exp (C ^ 2 * L ^ 2) *
        Real.exp (C * L * Real.exp ((14 / 10000 : ℝ) * L)) *
        Real.exp (C * L * Real.exp ((14 / 10000 : ℝ) * L)) *
        Real.exp (C * L * Real.exp ((14 / 10000 : ℝ) * L)) *
        Real.exp (C * L ^ 2) * Real.exp (C * L ^ 2) * Real.exp (C * L ^ 2) := by
      gcongr
    _ ≤ _ := by
      simp only [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h₁ := mul_le_mul_of_nonneg_right
        (show C ^ 2 + 3 * C ≤ 8 * C ^ 2 by nlinarith) (sq_nonneg L)
      have h₂ := mul_le_mul_of_nonneg_right
        (show 3 * C ≤ 8 * C ^ 2 by nlinarith) (mul_nonneg hL0 (Real.exp_nonneg ((14 / 10000 : ℝ) * L)))
      nlinarith

end Ostmann

end OAI
