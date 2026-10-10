import OAI.Analysis.FourierLLogL.Finite.Quadratic

/-! # More estimates on event probabilities -/
open Function Set Filter
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Law
open Real
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
open scoped Classical

lemma prob_mono (P : Law α) (p q : α → Prop) (h : ∀ i, p i → q i) : P.prob p ≤ P.prob q := by
  unfold prob; apply Ex_mono; intro i
  split_ifs with H H' H'
  · norm_num
  · exact (H' (h _ H)).elim
  · norm_num
  · norm_num

lemma prob_union (P : Law α) (p q : α → Prop) : P.prob (fun i => p i ∨ q i) ≤ P.prob p + P.prob q := by
  unfold prob; rw [← Ex_add]; apply Ex_mono; intro i
  by_cases H : p i <;> by_cases H' : q i <;> norm_num [H,H']

lemma prob_send (P : Law α) (f : α → β) (p : β → Prop) :
    (P.send f).prob p = P.prob fun x => p (f x) := by
  unfold prob; rw [Ex_send]

lemma upperTail (P : Law α) (p : α → Prop) (f : α → ℝ) (h : ∀ i, 0 ≤ f i)
    (r : ℝ) (he : ∀ i, p i → r ≤ f i) :
    r*P.prob p ≤ P.Ex f := by
  unfold prob; rw [← Ex_lmul]; apply Ex_mono; intro i
  split_ifs with H
  · rw [mul_one]; exact he i H
  · rw [mul_zero]; exact h i

lemma independent (P : Law α) (p : α → Prop) (T : ℕ) :
    (pack (fun _ : Fin T => P)).prob (fun i => ∀ k, p (i k)) =
    (P.prob p)^T := by
  classical
  have H (i : Fin T → α) :
      (if ∀ k, p (i k) then 1 else (0:ℝ)) =
        ∏ k, (if p (i k) then (1:ℝ) else 0) := by
    split_ifs with H
    · simp [H]
    push Not at H
    obtain ⟨x,hx⟩ := H
    exact Eq.symm (Finset.prod_eq_zero (i:=x) (Finset.mem_univ x) (by simp [hx]))

  have he : (pack (fun _ : Fin T => P)).prob (fun i => ∀ k, p (i k)) =
      (pack (fun _ : Fin T => P)).Ex (fun i => ∏ k, (if p (i k) then (1:ℝ) else 0)) := by
    rw [prob_eq]; simp_rw [Ex, ← H]
    simp
  rw [he]; unfold prob
  rw [pack_Ex_prod (fun _ : Fin T => P) (fun _ i => if p i then 1 else 0)]
  simp

lemma bernoulli_trial {x : ℝ} (h : 0 ≤ x) (hh : x ≤ 1) (m : ℕ) :
    ↑m * x^m * (1-x) ≤ 1 := by
  have H := geom_sum_mul_neg x m
  have H1 : m*x^m ≤ ∑ i∈Finset.range m, x^i := by
    calc
      _ = ∑ i∈Finset.range m, x^m := by simp
      _ ≤ _ := by
        exact Finset.sum_le_sum fun i hi => pow_le_pow_of_le_one h hh (Finset.mem_range.mp hi).le
  nlinarith [pow_nonneg h m, mul_le_mul_of_nonneg_right H1 (sub_nonneg.mpr hh)]

lemma lowerTail (P : Law α) (p : α → Prop) (h Hp : ℝ) (f : α → ℝ)
    (hh : ∀ i, p i → f i ≤ Hp+h) (hf : ∀ i, ¬p i → f i ≤ h) :
    P.Ex f ≤ Hp * P.prob p + h := by
  unfold prob
  refine le_trans (P.Ex_mono (g:=fun i => Hp*(if p i then 1 else 0)+h) (fun i => ?_)) ?_
  · split_ifs with H
    · rw [mul_one]; exact hh _ H
    rw [mul_zero,zero_add]; exact hf _ H
  rw [Ex_add,Ex_lmul,Ex_const]

end FourierLLogL.Law

end OAI
