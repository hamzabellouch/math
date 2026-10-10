import OAI.NumberTheory.Ostmann.Characters.CharacterHistoryWeight
import OAI.NumberTheory.Ostmann.Characters.TemplateGraphCore
import OAI.NumberTheory.Ostmann.Characters.TemplateHistory

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform ComplexConjugate
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable
open Arithmetic

def period (k j:ℕ) (x:State k j) : ℤ := ∏i,x i

def outsideProduct (k j:ℕ) (x:State k (j+1)) : ℤ :=
  ∏i:{i:(schedule k j).Slot // (schedule k j).IsOutside j i},x (.inr i)

theorem period_childState (k j:ℕ) (hj:j<k) (b:Bool) (x:State k (j+1)) (P:ℤ) :
    period k j (childState k j b x P)=P*copiedProduct k j b x*outsideProduct k j x := by
  unfold period
  rw [← (oldIndexEquiv (schedule k j) j (pivotSlot k j hj) (pivotSlot_unique k j hj)).prod_comp]
  rw [Fintype.prod_option,Fintype.prod_sum_type]
  change childState k j b x P (pivotSlot k j hj).val *
    ((∏i:{i:(schedule k j).Slot // (schedule k j).IsCopied j i},childState k j b x P i.val)*
      ∏i:{i:(schedule k j).Slot // (schedule k j).IsOutside j i},childState k j b x P i.val)=_
  simp only [childState_pivot k j b x P _ (pivotSlot k j hj).property,
    childState_copied,childState_outside,copiedProduct,outsideProduct,mul_assoc]

def leafWeight (k:ℕ) (X Δ W:ℝ) (s:ℤ) (x:State k 0) : ℂ :=
  if 0<(period k 0 x:ℝ) ∧ Real.log X+Δ-W≤Real.log (period k 0 x:ℝ) then
    (Real.sqrt (X/(period k 0 x:ℝ)):ℂ)*𝓕 SchwartzCutoff.psi (-(s:ℝ)*X/(period k 0 x:ℝ))
  else 0

theorem leafWeight_norm_le (k:ℕ) (X Δ W:ℝ) (hX:0<X) (s:ℤ) (x:State k 0) :
    ‖leafWeight k X Δ W s x‖≤leafFourierBound*Real.exp ((-Δ+W)/2) := by
  unfold leafWeight
  split_ifs with h
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ Real.sqrt (X/(period k 0 x:ℝ))*leafFourierBound :=
        mul_le_mul_of_nonneg_left (norm_fourier_psi_le _) (Real.sqrt_nonneg _)
      _ ≤ _ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left
          (sqrt_ratio_le_of_log_lower X (period k 0 x:ℝ) Δ W hX h.1 h.2) leafFourierBound_pos.le
  · rw [norm_zero]; exact mul_nonneg leafFourierBound_pos.le (Real.exp_pos _).le

def weight (k:ℕ) (mask:(j:ℕ)→ℤ→State k j→Prop) (X Δ W:ℝ) :
    (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→ℂ
  | 0,s,x,_ => if mask 0 s x then leafWeight k X Δ W s x else 0
  | j+1,s,x,t => if mask (j+1) s x then
      let P := reconstructedPivot k j x s t.1.1 t.1.2
      weight k mask X Δ W j t.1.1 (childState k j true x P) t.2.1 *
        conj (weight k mask X Δ W j t.1.2 (childState k j false x P) t.2.2)
    else 0

theorem weight_norm_le (k:ℕ) (mask:(j:ℕ)→ℤ→State k j→Prop)
    (X Δ W:ℝ) (hX:0<X) (j:ℕ) (s:ℤ) (x:State k j) (t:HistoryReconstruction.Tree j) :
    ‖weight k mask X Δ W j s x t‖≤(leafFourierBound*Real.exp ((-Δ+W)/2))^(2^j) := by
  have hC : 0≤leafFourierBound*Real.exp ((-Δ+W)/2) :=
    mul_nonneg leafFourierBound_pos.le (Real.exp_pos _).le
  induction j generalizing s with
  | zero =>
    change ‖if mask 0 s x then leafWeight k X Δ W s x else 0‖≤_
    split_ifs
    · simpa only [pow_zero,pow_one] using leafWeight_norm_le k X Δ W hX s x
    · rw [norm_zero]; positivity
  | succ j ih =>
    rw [weight]
    split_ifs
    · rw [norm_mul,Complex.norm_conj]
      calc
        _ ≤ (leafFourierBound*Real.exp ((-Δ+W)/2))^(2^j)*
            (leafFourierBound*Real.exp ((-Δ+W)/2))^(2^j) :=
          mul_le_mul (ih _ _ t.2.1) (ih _ _ t.2.2) (norm_nonneg _) (pow_nonneg hC _)
        _ = _ := by rw [← pow_add]; congr 1; omega
    · rw [norm_zero]; positivity

theorem weight_norm_sq_le (k:ℕ) (mask:(j:ℕ)→ℤ→State k j→Prop)
    (X Δ W:ℝ) (hX:0<X) (j:ℕ) (s:ℤ) (x:State k j) (t:HistoryReconstruction.Tree j) :
    ‖weight k mask X Δ W j s x t‖^2≤
      (leafFourierBound*Real.exp ((-Δ+W)/2))^((2^j)*2) := by
  simpa only [← pow_mul] using pow_le_pow_left₀ (norm_nonneg _)
    (weight_norm_le k mask X Δ W hX j s x t) 2

end Ostmann.Characters.Template

end

end OAI
