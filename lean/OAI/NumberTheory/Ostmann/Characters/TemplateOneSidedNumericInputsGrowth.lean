import Mathlib.Tactic.Ring
import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapAsymptotics

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedNumericInputs

theorem coefficient_pow_exp_le (M C t A : ℝ) (n : ℕ) (hM : 1 ≤ M) (hC : 0 ≤ C)
    (ht : t ≤ A*M) : C*M^n*Real.exp t ≤ Real.exp ((C+(n:ℝ)+A)*M) := by
  have hM0 : 0 ≤ M := by linarith
  have hcM : C ≤ C*M := le_mul_of_one_le_right hC hM
  have hce : C ≤ Real.exp (C*M) := by linarith [Real.add_one_le_exp (C*M)]
  have hMe : M ≤ Real.exp M := by linarith [Real.add_one_le_exp M]
  have hp : M^n ≤ Real.exp ((n:ℝ)*M) := by
    simpa only [←Real.exp_nat_mul] using pow_le_pow_left₀ hM0 hMe n
  have hprod := mul_le_mul hce hp (pow_nonneg hM0 n) (Real.exp_pos _).le
  calc
    _ ≤ (Real.exp (C*M)*Real.exp ((n:ℝ)*M))*Real.exp (A*M) :=
      mul_le_mul hprod (Real.exp_le_exp.mpr ht) (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring

theorem sum_three_le_exp (M A x y w : ℝ) (hM : 1 ≤ M)
    (hx : x ≤ Real.exp (A*M)) (hy : y ≤ Real.exp (A*M)) (hw : w ≤ Real.exp (A*M)) :
    x+y+w ≤ Real.exp ((A+3)*M) := by
  have h3 : (3:ℝ) ≤ Real.exp (3*M) := by linarith [Real.add_one_le_exp (3*M)]
  calc
    _ ≤ 3*Real.exp (A*M) := by linarith
    _ ≤ Real.exp (3*M)*Real.exp (A*M) := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

def rowLogHeight (C z β L : ℝ) : ℝ :=
  Real.exp (β*L)+Real.log 4+2*historyPolynomialCost C z 3 L

def rowHeightCoefficient (β z C : ℝ) : ℝ := β/z+2*C+|Real.log 4|+6

def numericCostCoefficient (β z C CD a W : ℝ) : ℝ :=
  CD+rowHeightCoefficient β z C+a+|W|+6

theorem rowHeightCoefficient_pos {β z C : ℝ} (hβ : 0 ≤ β) (hz : 0 < z) (hC : 0 ≤ C) :
    0 < rowHeightCoefficient β z C := by
  unfold rowHeightCoefficient
  positivity

theorem row_height_le_exp {β z C L M : ℝ} (hβ : 0 ≤ β) (hz : 0 < z) (hC : 0 ≤ C)
    (hM : 1 ≤ M) (hLM : z*L ≤ M) :
    Real.exp (β*L)+Real.log 4+2*C*M^3 ≤ Real.exp (rowHeightCoefficient β z C*M) := by
  have hM0 : 0 ≤ M := by linarith
  have hdiv : 0 ≤ β/z := div_nonneg hβ hz.le
  have hb : β*L ≤ (β/z)*M := by
    calc
      _ = (β/z)*(z*L) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hLM hdiv
  let A := β/z+2*C+|Real.log 4|+3
  have hA1 : β/z ≤ A := by dsimp [A]; linarith [abs_nonneg (Real.log 4)]
  have hA2 : |Real.log 4| ≤ A := by dsimp [A]; linarith
  have hA3 : 2*C+3 ≤ A := by dsimp [A]; linarith [abs_nonneg (Real.log 4)]
  have hx : Real.exp (β*L) ≤ Real.exp (A*M) :=
    Real.exp_le_exp.mpr (hb.trans (mul_le_mul_of_nonneg_right hA1 hM0))
  have hy0 : |Real.log 4| ≤ Real.exp (|Real.log 4| *M) := by
    have hh := le_mul_of_one_le_right (abs_nonneg (Real.log 4)) hM
    linarith [Real.add_one_le_exp (|Real.log 4| *M)]
  have hy : Real.log 4 ≤ Real.exp (A*M) :=
    (le_abs_self _).trans (hy0.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA2 hM0)))
  have hp0 : 2*C*M^3 ≤ Real.exp ((2*C+3)*M) := by
    simpa only [Real.exp_zero,mul_one,Nat.cast_ofNat,add_zero] using
      coefficient_pow_exp_le M (2*C) 0 0 3 hM (by positivity) (by simp)
  have hp : 2*C*M^3 ≤ Real.exp (A*M) :=
    hp0.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA3 hM0))
  simpa only [A,rowHeightCoefficient,show (β/z+2*C+|Real.log 4|+3)+3=
    β/z+2*C+|Real.log 4|+6 by ring] using sum_three_le_exp M A _ _ _ hM hx hy hp

theorem numeric_inputs_cost {β z C CD a : ℝ} (W : ℝ)
    (hβ : 0 ≤ β) (hz : 0 < z) (hC : 0 ≤ C) (hCD : 0 ≤ CD) (ha : 0 ≤ a) :
    0 < numericCostCoefficient β z C CD a W ∧
    ∀ L : ℝ,
      rowLogHeight C z β L ≤ Real.exp (historyPolynomialCost (numericCostCoefficient β z C CD a W) z 4 L) ∧
      ∀ D : ℝ,0 ≤ D → D ≤ CD*(1+(⌊z*L⌋₊:ℝ)) →
        D*rowLogHeight C z β L+|a*(⌊z*L⌋₊:ℝ)|+|W| ≤
          Real.exp (historyPolynomialCost (numericCostCoefficient β z C CD a W) z 4 L) := by
  have hK := rowHeightCoefficient_pos hβ hz hC
  have hC' : 0 < numericCostCoefficient β z C CD a W := by
    unfold numericCostCoefficient
    linarith [abs_nonneg W]
  refine ⟨hC',?_⟩
  intro L
  let M : ℝ := 1+(⌊z*L⌋₊:ℝ)
  let K := rowHeightCoefficient β z C
  let A := CD+K+a+|W|+2
  let C' := numericCostCoefficient β z C CD a W
  have hM : 1 ≤ M := by dsimp [M]; linarith [Nat.cast_nonneg (α:=ℝ) ⌊z*L⌋₊]
  have hM0 : 0 ≤ M := by linarith
  have hLM : z*L ≤ M := by
    simpa only [M,add_comm] using (Nat.lt_floor_add_one (z*L)).le
  have hheight : rowLogHeight C z β L ≤ Real.exp (K*M) := by
    simpa only [rowLogHeight,historyPolynomialCost,M,K,mul_assoc] using row_height_le_exp hβ hz hC hM hLM
  have hM4 : M ≤ M^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hM (show 1 ≤ 4 by decide)
  have hKC : K ≤ C' := by dsimp [K,C',numericCostCoefficient]; linarith [abs_nonneg W]
  have hAC : A+3 ≤ C' := by dsimp [A,C',numericCostCoefficient,K]; linarith
  have hKM : K*M ≤ C'*M^4 :=
    (mul_le_mul_of_nonneg_right hKC hM0).trans (mul_le_mul_of_nonneg_left hM4 hC'.le)
  refine ⟨hheight.trans (Real.exp_le_exp.mpr hKM),?_⟩
  intro D hD hDb
  have hDexp : D ≤ Real.exp ((CD+1)*M) := by
    have h := coefficient_pow_exp_le M CD 0 0 1 hM hCD (by simp)
    simp only [pow_one,Real.exp_zero,mul_one,Nat.cast_one,add_zero] at h
    exact hDb.trans h
  have hprod : D*rowLogHeight C z β L ≤ Real.exp ((CD+1+K)*M) := by
    calc
      _ ≤ D*Real.exp (K*M) := mul_le_mul_of_nonneg_left hheight hD
      _ ≤ Real.exp ((CD+1)*M)*Real.exp (K*M) := mul_le_mul_of_nonneg_right hDexp (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  have hDa : CD+1+K ≤ A := by dsimp [A]; linarith [abs_nonneg W]
  have haa : a+1 ≤ A := by dsimp [A,K]; linarith [abs_nonneg W]
  have hWa : |W| ≤ A := by dsimp [A,K]; linarith
  have hΔ : |a*(⌊z*L⌋₊:ℝ)| ≤ Real.exp ((a+1)*M) := by
    rw [abs_of_nonneg (mul_nonneg ha (Nat.cast_nonneg _))]
    have h := coefficient_pow_exp_le M a 0 0 1 hM ha (by simp)
    simp only [pow_one,Real.exp_zero,mul_one,Nat.cast_one,add_zero] at h
    apply le_trans _ h
    apply mul_le_mul_of_nonneg_left _ ha
    dsimp [M]
    linarith
  have hW : |W| ≤ Real.exp (|W| *M) := by
    have hh := le_mul_of_one_le_right (abs_nonneg W) hM
    linarith [Real.add_one_le_exp (|W| *M)]
  have hsum := sum_three_le_exp M A _ _ _ hM
    (hprod.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hDa hM0)))
    (hΔ.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right haa hM0)))
    (hW.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hWa hM0)))
  exact hsum.trans (Real.exp_le_exp.mpr
    ((mul_le_mul_of_nonneg_right hAC hM0).trans (mul_le_mul_of_nonneg_left hM4 hC'.le)))

end Ostmann.Characters.TemplateOneSidedNumericInputs

end

end OAI
