import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.QueryDelta
import OAI.Probability.CriticalPercolation.ProductMeasure.ExpectClosedFlip

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def closedPivotWeight (T : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (e : E) : ℝ :=
  if ¬ω e ∧ openPivot F e (Function.update ω e True) then p*T.queryDelta F w ω e else 0

theorem contact_flip_identity (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (ψ : ℝ → ℝ) :
    expect w (fun ω => ∑ e, T.closedPivotWeight p F w ω e *
      ψ (T.score p F w (Function.update ω e True))) =
      expect w (fun ω => T.score p F w ω * ψ (T.score p F w ω)) := by
  have hsingle (e : E) :
      expect w (fun ω => T.closedPivotWeight p F w ω e *
        ψ (T.score p F w (Function.update ω e True))) =
      expect w (fun ω => (if openPivot F e ω then (1-p)*T.queryDelta F w ω e else 0) *
        ψ (T.score p F w ω)) := by
    have h := expect_closed_flip_decidable w hw e hp (h0 e) (h1 e)
      (fun ω => (if openPivot F e ω then T.queryDelta F w ω e else 0) * ψ (T.score p F w ω))
    convert h using 1
    · congr 1
      funext ω
      let σ : Set E := ω
      change T.closedPivotWeight p F w σ e * ψ (T.score p F w (Function.update σ e True)) =
        if ¬σ e then p*((if openPivot F e (Function.update σ e True) then
          T.queryDelta F w (Function.update σ e True) e else 0) *
          ψ (T.score p F w (Function.update σ e True))) else 0
      rw [queryDelta_update T F w σ e True]
      simp only [closedPivotWeight]
      by_cases hc : σ e <;>
        by_cases hpiv : openPivot F e (Function.update σ e True) <;> simp [hc,hpiv,mul_assoc]
    · congr 1
      funext ω
      by_cases hpiv : openPivot F e ω
      · simp only [ite_eq_left hpiv,ite_eq_left hpiv.1]; ring
      · simp only [ite_eq_right hpiv,mul_zero,zero_mul,ite_self]
  rw [expect_sum]
  simp_rw [hsingle]
  rw [← expect_sum]
  congr 1
  funext ω
  rw [← Finset.sum_mul]
  exact congrArg (fun x => x * ψ (T.score p F w ω))
    (score_eq_queryDelta_sum T used hT p F w ω).symm

end CriticalPercolation.SearchTree

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def prefixScore (T : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (e : E) : ℝ :=
  match T with
  | .done _ => 0
  | .ask f l r => (if openPivot F f ω then (1-p)*delta w F f else 0) +
      if e = f then 0 else
        if ω f then r.prefixScore p F (pin w f True) ω e
        else l.prefixScore p F (pin w f False) ω e

lemma prefixScore_le (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) (e : E) :
    T.prefixScore p F w ω e ≤ T.score p F w ω := by
  induction T generalizing used w with
  | done _ => exact le_rfl
  | ask f l r hl hr =>
    simp only [prefixScore,score]
    apply add_le_add_right
    by_cases he : e = f
    · rw [ite_eq_left he]
      by_cases ho : ω f
      · rw [ite_eq_left ho]
        exact score_nonneg r _ hT.2.2 hp F hF _ (pin_normalized w hw f True)
          (pin_nonneg w hn f True) (fresh_pin w p used hf f True) ω
      · rw [ite_eq_right ho]
        exact score_nonneg l _ hT.2.1 hp F hF _ (pin_normalized w hw f False)
          (pin_nonneg w hn f False) (fresh_pin w p used hf f False) ω
    · rw [ite_eq_right he]
      by_cases ho : ω f
      · rw [ite_eq_left ho,ite_eq_left ho]
        exact hr _ hT.2.2 _ (pin_normalized w hw f True) (pin_nonneg w hn f True)
          (fresh_pin w p used hf f True)
      · rw [ite_eq_right ho,ite_eq_right ho]
        exact hl _ hT.2.1 _ (pin_normalized w hw f False) (pin_nonneg w hn f False)
          (fresh_pin w p used hf f False)

lemma closedPivotWeight_nonneg (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) (e : E) : 0 ≤ T.closedPivotWeight p F w ω e := by
  unfold closedPivotWeight
  split_ifs
  · exact mul_nonneg hp.1.le (queryDelta_nonneg T used hT hp F hF w hw hn hf ω e)
  · exact le_rfl

theorem marked_prefix_bound (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    expect w (fun ω => ∑ e, T.closedPivotWeight p F w ω e *
      (1 + T.prefixScore p F w (Function.update ω e True) e)) ≤
      expect w (T.score p F w) + expect w (fun ω => (T.score p F w ω)^2) := by
  calc
    _ ≤ expect w (fun ω => ∑ e, T.closedPivotWeight p F w ω e *
        (1 + T.score p F w (Function.update ω e True))) := by
      apply expect_mono hn
      intro ω
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right (prefixScore_le T used hT hp F hF w hw hn hf _ e) 1)
        (closedPivotWeight_nonneg T used hT hp F hF w hw hn hf ω e)
    _ = expect w (fun ω => T.score p F w ω * (1 + T.score p F w ω)) :=
      contact_flip_identity T used hT hp F w hw h0 h1 (fun x => 1+x)
    _ = expect w (fun ω => T.score p F w ω + (T.score p F w ω)^2) := by
      congr 1
      funext ω
      ring
    _ = _ := expect_add w _ _

end CriticalPercolation.SearchTree

end
end

end OAI
