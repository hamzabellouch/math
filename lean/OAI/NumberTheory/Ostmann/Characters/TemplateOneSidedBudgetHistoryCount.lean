import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetModulus

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedBudget
open HistoryFrequencyLabels HistoryFrequencyBudget FrequencyTreeSum
attribute [local instance] Classical.propDecidable

def fullNodeCount : ℕ → ℕ
  | 0 => 1
  | j+1 => 1+2*fullNodeCount j

theorem fullNodeCount_add_one (j : ℕ) : fullNodeCount j+1=2^(j+1) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [fullNodeCount,pow_succ];omega

theorem assignment_card_le_exp (S : List Bool → Finset ℤ) (H : ℝ)
    (hS : ∀q,((S q).card:ℝ) ≤ Real.exp H) (j : ℕ) (p : List Bool) :
    (Fintype.card (Assignment S j p):ℝ) ≤ Real.exp ((fullNodeCount j:ℝ)*H) := by
  induction j generalizing p with
  | zero => simpa only [Assignment,Fintype.card_coe,fullNodeCount,Nat.cast_one,one_mul] using hS p
  | succ j ih =>
    change (Fintype.card ({s:ℤ //s∈S p} ×
      (Assignment S j (false::p) × Assignment S j (true::p))):ℝ) ≤ _
    rw [Fintype.card_prod,Fintype.card_prod,Fintype.card_coe,Nat.cast_mul,Nat.cast_mul]
    have hh := mul_le_mul (hS p)
      (mul_le_mul (ih (false::p)) (ih (true::p)) (Nat.cast_nonneg _) (Real.exp_pos _).le)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.exp_pos _).le
    apply hh.trans_eq
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    simp only [fullNodeCount,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    ring

theorem supportedHistory_card_le_exp {a m : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m) (j : ℕ) :
    (Fintype.card (SupportedHistory (ranges a m j) j []):ℝ) ≤
      Real.exp ((fullNodeCount j:ℝ)*(Real.log 2+linearEnvelope a j*m)) := by
  rw [← Fintype.card_congr (assignmentEquiv (ranges a m j) j [])]
  apply assignment_card_le_exp
  intro q
  change ((signedRange (bound a m (j-q.length))).card:ℝ) ≤ _
  rw [signedRange_card,Nat.cast_mul,Nat.cast_ofNat,Real.exp_add,
    Real.exp_log (by norm_num : (0:ℝ)<2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (bound_le_exp _ _ _).trans
    (Real.exp_le_exp.mpr (exponent_le_linear ha hm (Nat.sub_le _ _)))

theorem supportedHistory_card_le_linear_exp {a m : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m) (j : ℕ) :
    (Fintype.card (SupportedHistory (ranges a m j) j []):ℝ) ≤
      Real.exp (((fullNodeCount j:ℝ)*(Real.log 2+linearEnvelope a j))*(1+m)) := by
  apply (supportedHistory_card_le_exp ha hm j).trans
  apply Real.exp_le_exp.mpr
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hA := (linearEnvelope_pos ha j).le
  have hn : 0 ≤ (fullNodeCount j:ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (fullNodeCount j:ℝ)*((Real.log 2+linearEnvelope a j)*(1+m)) := by
      apply mul_le_mul_of_nonneg_left _ hn
      nlinarith
    _ = _ := by ring

theorem supportedHistory_pair_card_le_exp {a m : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m) (j : ℕ) :
    (Fintype.card (SupportedHistory (ranges a m j) j [] ×
      SupportedHistory (ranges a m j) j []):ℝ) ≤
      Real.exp ((2*(fullNodeCount j:ℝ)*(Real.log 2+linearEnvelope a j))*(1+m)) := by
  rw [Fintype.card_prod,Nat.cast_mul]
  have hh := supportedHistory_card_le_linear_exp ha hm j
  apply (mul_le_mul hh hh (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
  rw [←Real.exp_add]
  congr 1
  ring

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
