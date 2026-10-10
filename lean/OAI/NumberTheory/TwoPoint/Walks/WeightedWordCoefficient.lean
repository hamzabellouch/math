import OAI.NumberTheory.TwoPoint.Bounds.PaddingStateWeights
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedWordIdentity

namespace OAI

/-! The coefficient table in the finite-state expansion is the literal
retained padding product times the signed centered-prime product. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def centeredWordBits {R J : ℕ} (p : Fin R → Fin J → ℕ)
    (bits : BooleanCube (R * J)) : ℝ :=
  ∏ i : Fin R, ∏ j : Fin J,
    ((if bits (finProdFinEquiv (i, j)) then 1 else 0) - (p i j : ℝ)⁻¹)

lemma centeredWordBits_abs_le {R J : ℕ} (p : Fin R → Fin J → ℕ)
    (hp : ∀ i j, (p i j).Prime) (bits : BooleanCube (R * J)) :
    |centeredWordBits p bits| ≤ 1 := by
  unfold centeredWordBits
  simp only [abs_prod]
  apply prod_le_one₀
  · intro i _
    positivity
  · intro i _
    apply prod_le_one₀
    · intro j _
      exact abs_nonneg _
    · intro j _
      have hpos : (0 : ℝ) < p i j := by exact_mod_cast (hp i j).pos
      have hone : (1 : ℝ) ≤ p i j := by exact_mod_cast (hp i j).one_lt.le
      have hinv : (p i j : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr hone
      cases bits (finProdFinEquiv (i, j)) <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · simpa only [zero_sub, abs_neg, abs_of_nonneg (inv_nonneg.mpr hpos.le)] using hinv
      · rw [abs_of_nonneg (by linarith : 0 ≤ 1 - (p i j : ℝ)⁻¹)]
        linarith [inv_nonneg.mpr hpos.le]

noncomputable def actualWordCoefficient {R J m : ℕ}
    (Qp Q : Finset ℕ) (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop)
    (L K : ℝ) (step : Fin R → SignedStep) (p : Fin R → Fin J → ℕ)
    (S : Fin (R + 1) → Finset (Fin m)) (bits : BooleanCube (R * J)) : ℝ :=
  (∏ i : Fin R, paddingStateDeparture Qp Q e eligible L K (step i)
    (S i.castSucc) (S i.succ)) * centeredWordBits p bits

lemma actualWordCoefficient_abs_le {R J m : ℕ}
    (Qp Q : Finset ℕ) (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop)
    (L K : ℝ) (step : Fin R → SignedStep) (p : Fin R → Fin J → ℕ)
    (hp : ∀ i j, (p i j).Prime) (hL : 0 ≤ L)
    (S : Fin (R + 1) → Finset (Fin m)) (bits : BooleanCube (R * J)) :
    |actualWordCoefficient Qp Q e eligible L K step p S bits| ≤
      ∏ i : Fin R, L * actualPaddingCoefficient (step i).padding := by
  rw [actualWordCoefficient, abs_mul, abs_prod]
  calc
    _ ≤ (∏ i : Fin R, L * actualPaddingCoefficient (step i).padding) * 1 := by
      apply mul_le_mul _ (centeredWordBits_abs_le p hp bits) (abs_nonneg _)
        (prod_nonneg (fun i _ => mul_nonneg hL (actualPaddingCoefficient_nonneg _)))
      apply prod_le_prod₀
      · intro i _
        exact abs_nonneg _
      · intro i _
        rw [abs_of_nonneg (paddingStateDeparture_nonneg Qp Q e eligible L K _ _ _ hL)]
        exact paddingStateDeparture_le Qp Q e eligible L K _ _ _ hL
    _ = _ := mul_one _

lemma actualWordCoefficient_budget {R J m : ℕ}
    (Qp Q : Finset ℕ) (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop)
    (L K : ℝ) (step : Fin R → SignedStep) (p : Fin R → Fin J → ℕ)
    (hp : ∀ i j, (p i j).Prime) (hL : 4800 ≤ L) (hR : (R : ℝ) ≤ 4 * L)
    (hdeg : ∀ i, ((step i).padding.primeFactors.card : ℝ) ≤ 100 * Real.log L)
    (S : Fin (R + 1) → Finset (Fin m)) (bits : BooleanCube (R * J)) :
    |actualWordCoefficient Qp Q e eligible L K step p S bits| ≤ Real.exp (L ^ 4) := by
  have hLp : 0 ≤ L := by linarith
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hLexp : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hu (i : Fin R) : L * actualPaddingCoefficient (step i).padding ≤ Real.exp (401 * L) := by
    have hd : actualPaddingCoefficient (step i).padding ≤ Real.exp (400 * L) := by
      unfold actualPaddingCoefficient
      calc
        _ ≤ (Real.exp 4) ^ (step i).padding.primeFactors.card :=
          pow_le_pow_left₀ (by norm_num) hfour _
        _ = Real.exp ((step i).padding.primeFactors.card * 4) := by rw [Real.exp_nat_mul]
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [hdeg i])
    calc
      _ ≤ Real.exp L * Real.exp (400 * L) :=
        mul_le_mul hLexp hd (actualPaddingCoefficient_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (actualWordCoefficient_abs_le Qp Q e eligible L K step p hp hLp S bits).trans
  calc
    _ ≤ ∏ _i : Fin R, Real.exp (401 * L) :=
      prod_le_prod₀ (fun i _ => mul_nonneg hLp (actualPaddingCoefficient_nonneg _)) (fun i _ => hu i)
    _ = Real.exp ((R : ℝ) * (401 * L)) := by simp only [prod_const, card_univ,
      Fintype.card_fin, Real.exp_nat_mul]
    _ ≤ Real.exp (1604 * L ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hR (show 0 ≤ 401 * L by positivity)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh : 1604 ≤ L ^ 2 := by nlinarith
      nlinarith [mul_nonneg (show 0 ≤ L ^ 2 - 1604 by linarith) (sq_nonneg L)]

end TwoPointCorrelations

end OAI
