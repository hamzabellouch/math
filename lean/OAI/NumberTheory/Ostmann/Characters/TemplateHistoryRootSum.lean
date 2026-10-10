import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyLabels
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWeight

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

def historyRootSum (k j:ℕ) (S:List Bool→Finset ℤ) (p:List Bool)
    (B V:(l:ℕ)→State k (l+1)→ℤ)
    (extra:(l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask:(l:ℕ)→ℤ→State k l→Prop) (X Δ W:ℝ) (s:ℤ) (x:State k j)
    (phase:SupportedHistory S j p→ℂ) : ℂ :=
  ∑h:SupportedHistory S j p,if h.val.1=s then
    retainedHistoryWeight k B V extra mask X Δ W j h.val.1 x h.val.2*phase h else 0

theorem retained_same_root_unique (k j:ℕ) (S:List Bool→Finset ℤ) (p:List Bool)
    (B V:(l:ℕ)→State k (l+1)→ℤ)
    (extra:(l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask:(l:ℕ)→ℤ→State k l→Prop) (X Δ W:ℝ) (x:State k j)
    (h h':SupportedHistory S j p) (hr:h.val.1=h'.val.1)
    (hh:retainedHistoryWeight k B V extra mask X Δ W j h.val.1 x h.val.2≠0)
    (hh':retainedHistoryWeight k B V extra mask X Δ W j h'.val.1 x h'.val.2≠0) : h=h' := by
  have ht := (retainedHistoryWeight_support hh).supported j
  have ht' := (retainedHistoryWeight_support hh').supported j
  rw [← hr] at ht'
  exact Subtype.ext (Prod.ext hr (supported_unique k B V j h.val.1 x h.val.2 h'.val.2 ht ht'))

theorem norm_sum_sq_eq_sum_sq_of_unique {ι:Type*} [Fintype ι] (f:ι→ℂ)
    (h:∀i j,f i≠0→f j≠0→i=j) : ‖∑i,f i‖^2=∑i,‖f i‖^2 := by
  by_cases he:∃i,f i≠0
  · obtain ⟨i,hi⟩ := he
    have hz (j:ι) (hj:j≠i) : f j=0 := by
      by_contra hne
      exact hj (h j i hne hi)
    rw [Finset.sum_eq_single i (fun j _ hj=>hz j hj) (by simp)]
    symm
    exact Finset.sum_eq_single i (fun j _ hj=>by rw [hz j hj,norm_zero]; norm_num) (by simp)
  · push Not at he
    simp only [he,Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0)]

theorem historyRootSum_norm_sq_le (k j:ℕ) (S:List Bool→Finset ℤ) (p:List Bool)
    (B V:(l:ℕ)→State k (l+1)→ℤ)
    (extra:(l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask:(l:ℕ)→ℤ→State k l→Prop) (X Δ W:ℝ) (s:ℤ) (x:State k j)
    (phase:SupportedHistory S j p→ℂ) (hphase:∀h,‖phase h‖≤1) :
    ‖historyRootSum k j S p B V extra mask X Δ W s x phase‖^2 ≤
      ∑h:SupportedHistory S j p,if h.val.1=s then
        ‖retainedHistoryWeight k B V extra mask X Δ W j h.val.1 x h.val.2‖^2 else 0 := by
  unfold historyRootSum
  rw [norm_sum_sq_eq_sum_sq_of_unique _ (by
    intro h h' hh hh'
    have hr:h.val.1=s := by
      by_contra hn
      exact hh (ite_eq_right hn)
    have hr':h'.val.1=s := by
      by_contra hn
      exact hh' (ite_eq_right hn)
    rw [ite_eq_left hr] at hh
    rw [ite_eq_left hr'] at hh'
    exact retained_same_root_unique k j S p B V extra mask X Δ W x h h' (hr.trans hr'.symm)
      (mul_ne_zero_iff.mp hh).1 (mul_ne_zero_iff.mp hh').1)]
  apply Finset.sum_le_sum
  intro h hh
  split_ifs
  · rw [norm_mul,mul_pow]
    calc
      _ ≤ ‖retainedHistoryWeight k B V extra mask X Δ W j h.val.1 x h.val.2‖^2*1 :=
        mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg (phase h),hphase h]) (sq_nonneg _)
      _ = _ := mul_one _
  · simp only [norm_zero,zero_pow (by decide : 2≠0),le_refl]

end Ostmann.Characters.Template

end

end OAI
