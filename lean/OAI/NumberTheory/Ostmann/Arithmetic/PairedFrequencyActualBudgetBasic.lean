import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightScaleNumerics
import OAI.NumberTheory.Ostmann.Arithmetic.PairedFrequencyTreeSumCount
import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetAbsorption
import OAI.NumberTheory.Ostmann.Conclusion.FinalRateAbsorptionBasic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.PairedFrequencyActualBudget
open Conclusion Characters

def addressBound (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) (l : ℕ) (p : List Bool) : ℕ :=
  frequencyBound Bs BD Bz k L (l-p.length)

def pairedRanges (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) (l : ℕ)
    (p : List Bool) : Finset (ℤ × ℤ) :=
  let S := HistoryFrequencyBudget.signedRange (addressBound Bs BD Bz k L l p)
  S ×ˢ S

theorem mem_pairedRanges (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) (l : ℕ)
    (p : List Bool) (s : ℤ × ℤ) :
    s∈pairedRanges Bs BD Bz k L l p ↔
      (s.1≠0 ∧ s.1.natAbs≤addressBound Bs BD Bz k L l p) ∧
      (s.2≠0 ∧ s.2.natAbs≤addressBound Bs BD Bz k L l p) := by
  simp [pairedRanges,HistoryFrequencyBudget.mem_signedRange]

@[simp] theorem pairedRanges_card (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) (l : ℕ)
    (p : List Bool) :
    (pairedRanges Bs BD Bz k L l p).card=(2*addressBound Bs BD Bz k L l p)^2 := by
  simp [pairedRanges,HistoryFrequencyBudget.signedRange_card,pow_two]

theorem addressBound_pos {Bs BD Bz : ℝ} (hBs : 0≤Bs) (hBD : 0≤BD) (hBz : 0≤Bz)
    {k : ℕ} (hk : 0<k) (L : ℝ) (l : ℕ) (p : List Bool) :
    1≤addressBound Bs BD Bz k L l p := by
  unfold addressBound frequencyBound
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  simpa using Real.one_le_exp (frequencyBudget_nonneg hBs hBD hBz hk L _)

theorem addressBound_le_exp (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) (l : ℕ)
    (hl : l≤k) (hm : 1≤bulkSize k L) (p : List Bool) :
    (addressBound Bs BD Bz k L l p : ℝ)≤
      Real.exp (scaleLinearConstant Bs BD Bz k*(bulkSize k L : ℝ)) :=
  (Nat.floor_le (Real.exp_pos _).le).trans
    (Real.exp_le_exp.mpr (frequencyBudget_le_linear Bs BD Bz k L hm ((Nat.sub_le _ _).trans hl)))

theorem budget_exp_bound {α : Type*} [DecidableEq α]
    (S : List Bool→Finset α) (C : List Bool→ℝ)
    (N : ℕ) (A B : ℝ) (hC : ∀p,0≤C p)
    (hnode : ∀p,C p≤Real.exp B)
    (hleaf : ∀p,p.length=N→((S p).card:ℝ)≤Real.exp A)
    (j : ℕ) (p : List Bool) (hp : j+p.length=N) :
    FrequencyTreeSum.budget S C j p≤Real.exp ((2:ℝ)^j*A+((2:ℝ)^j-1)*B) := by
  have hn (j : ℕ) (p : List Bool) : 0≤FrequencyTreeSum.budget S C j p := by
    induction j generalizing p with
    | zero => exact Nat.cast_nonneg _
    | succ j ih => exact mul_nonneg (mul_nonneg (hC p) (ih _)) (ih _)
  induction j generalizing p with
  | zero => simpa only [FrequencyTreeSum.budget,pow_zero,one_mul,sub_self,zero_mul,add_zero]
      using hleaf p (by omega)
  | succ j ih =>
    have hl := ih (false::p) (by simp only [List.length_cons]; omega)
    have hr := ih (true::p) (by simp only [List.length_cons]; omega)
    calc
      _≤Real.exp B*Real.exp ((2:ℝ)^j*A+((2:ℝ)^j-1)*B)*
          Real.exp ((2:ℝ)^j*A+((2:ℝ)^j-1)*B) :=
        mul_le_mul (mul_le_mul (hnode p) hl (hn _ _) (Real.exp_pos _).le)
          hr (hn _ _) (by positivity)
      _=_ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; rw [pow_succ]; ring

end Ostmann.Arithmetic.PairedFrequencyActualBudget

end

end OAI
