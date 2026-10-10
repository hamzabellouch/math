import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedFlagBudgetsHeight

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedFlagBudgets
open Construction HistorySymbolicEncoding HistoryPairFlags

theorem selected_frequencyBound_log_le (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (hm : 1 ≤ Conclusion.bulkSize k L) {l : ℕ} (hl : l ≤ k) :
    Real.log (HistoryHeightBudgetFixed.frequencyBound (Conclusion.frequencyBound Bs BD Bz k L) l) ≤ 
      Conclusion.scaleLinearConstant Bs BD Bz k*(Conclusion.bulkSize k L:ℝ) := by
  let C := Conclusion.scaleLinearConstant Bs BD Bz k
  let m : ℝ := Conclusion.bulkSize k L
  have hcm : 0 ≤ C*m := mul_nonneg (Conclusion.scaleLinearConstant_pos Bs BD Bz k).le (Nat.cast_nonneg _)
  have hs : (Finset.range (l+1)).sup (Conclusion.frequencyBound Bs BD Bz k L) ≤ ⌊Real.exp (C*m)⌋₊ := by
    apply Finset.sup_le
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact Nat.floor_mono (Real.exp_le_exp.mpr
      (Conclusion.frequencyBudget_le_linear Bs BD Bz k L hm ((by omega : i ≤ l).trans hl)))
  have hsr : (((Finset.range (l+1)).sup (Conclusion.frequencyBound Bs BD Bz k L):ℕ):ℝ) ≤ Real.exp (C*m) :=
    (Nat.cast_le.mpr hs).trans (Nat.floor_le (Real.exp_nonneg _))
  have hh : HistoryHeightBudgetFixed.frequencyBound (Conclusion.frequencyBound Bs BD Bz k L) l ≤ 
      Real.exp (C*m) := max_le (Real.one_le_exp hcm) hsr
  exact (Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one
    (HistoryHeightBudgetFixed.one_le_frequencyBound _ _))).mpr hh

def logarithmicCoefficient (k : ℕ) (C : ℝ) : ℝ :=
  (Real.log 3+4*(heightCoefficient k:ℝ)*(Real.log 2+C+1))/Real.log 2

theorem logarithmicCoefficient_nonneg (k : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ logarithmicCoefficient k C := by
  have h₂ := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  have h₃ := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
  unfold logarithmicCoefficient
  positivity

theorem envelope_log_div_le {b k l : ℕ} {h g : History l} (V : ℕ → ℕ)
    {B C m H : ℝ}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hl : l ≤ k)
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hm : 0 ≤ m) (hb : (b:ℝ) ≤ m) (hH : 0 ≤ H)
    (hfreq : Real.log (HistoryHeightBudgetFixed.frequencyBound V l) ≤ C*m)
    (hlogB : Real.log B ≤ Real.exp H) :
    max 0 (Real.log (envelope h g V B))/Real.log 2  ≤ 
      logarithmicCoefficient k C*(m+1)^2*Real.exp H := by
  let M := m+1
  let X := Real.exp H
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hX : 1 ≤ X := Real.one_le_exp hH
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have h₂ := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  have h₃ := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
  have hmM : m ≤ M := by dsimp [M]; linarith
  have ht : Real.log 2+Real.log (HistoryHeightBudgetFixed.frequencyBound V l)+Real.log B ≤ 
      (Real.log 2+C+1)*M*X := by
    have ht₂ : Real.log 2 ≤ Real.log 2*M*X :=
      (le_mul_of_one_le_right h₂ hM).trans (le_mul_of_one_le_right (mul_nonneg h₂ hM0) hX)
    have htC : C*m ≤ C*M*X :=
      (mul_le_mul_of_nonneg_left hmM hC).trans (le_mul_of_one_le_right (mul_nonneg hC hM0) hX)
    have htX : X ≤ M*X := le_mul_of_one_le_left hX0 hM
    calc
      _  ≤  Real.log 2*M*X+C*M*X+M*X := by linarith
      _ = _ := by ring
  have hcb : (heightCoefficient k:ℝ)*(b+1) ≤ (heightCoefficient k:ℝ)*M :=
    mul_le_mul_of_nonneg_left (by dsimp [M]; linarith) (Nat.cast_nonneg _)
  have ht0 : 0 ≤ (Real.log 2+C+1)*M*X := by positivity
  have hcore := mul_le_mul hcb ht
    (add_nonneg (add_nonneg h₂ (Real.log_nonneg (HistoryHeightBudgetFixed.one_le_frequencyBound _ _)))
      (Real.log_nonneg hB)) (by positivity : 0 ≤ (heightCoefficient k:ℝ)*M)
  have hM2 : 1 ≤ M^2 := one_le_pow₀ hM
  have hthree : Real.log 3 ≤ Real.log 3*M^2*X :=
    (le_mul_of_one_le_right h₃ hM2).trans (le_mul_of_one_le_right (mul_nonneg h₃ (sq_nonneg M)) hX)
  have he := envelope_log_le V hh hg hl hB
  have hn : max 0 (Real.log (envelope h g V B)) ≤ 
      (Real.log 3+4*(heightCoefficient k:ℝ)*(Real.log 2+C+1))*M^2*X := by
    calc
      _  ≤  Real.log 3+4*(((heightCoefficient k:ℝ)*M)*((Real.log 2+C+1)*M*X)) := by linarith
      _  ≤  Real.log 3*M^2*X+4*(((heightCoefficient k:ℝ)*M)*((Real.log 2+C+1)*M*X)) := by linarith
      _ = _ := by ring
  have hd := div_le_div_of_nonneg_right hn (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  dsimp [logarithmicCoefficient,M,X] at hd ⊢
  convert hd using 1; ring

theorem quadratic_prefactor_le_exp {D M H : ℝ} (hD : 0 ≤ D) (hM : 1 ≤ M) :
    D*M^2*Real.exp H ≤ Real.exp ((D+2)*M+H) := by
  have hDe : D ≤ Real.exp (D*M) :=
    (by linarith : D ≤ D+1).trans ((Real.add_one_le_exp D).trans
      (Real.exp_le_exp.mpr (le_mul_of_one_le_right hD hM)))
  have hMe : M ≤ Real.exp M := (by linarith : M ≤ M+1).trans (Real.add_one_le_exp M)
  have hM2 : M^2 ≤ Real.exp (2*M) := by
    change M^2  ≤  Real.exp (((2:ℕ):ℝ)*M)
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith : 0 ≤ M) hMe 2
  calc
    _  ≤  Real.exp (D*M)*Real.exp (2*M)*Real.exp H := by
      gcongr
    _ = _ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring

theorem envelope_log_div_le_exp {b k l : ℕ} {h g : History l} (V : ℕ → ℕ)
    {B C m H : ℝ}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hl : l ≤ k)
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hm : 0 ≤ m) (hb : (b:ℝ) ≤ m) (hH : 0 ≤ H)
    (hfreq : Real.log (HistoryHeightBudgetFixed.frequencyBound V l) ≤ C*m)
    (hlogB : Real.log B ≤ Real.exp H) :
    max 0 (Real.log (envelope h g V B))/Real.log 2  ≤ 
      Real.exp ((logarithmicCoefficient k C+2)*(m+1)+H) :=
  (envelope_log_div_le V hh hg hl hB hC hm hb hH hfreq hlogB).trans
    (quadratic_prefactor_le_exp (logarithmicCoefficient_nonneg k hC) (by linarith))

end Ostmann.Arithmetic.HistorySelectedFlagBudgets

end

end OAI
