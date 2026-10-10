import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.ClosedPivotWeight
import OAI.Probability.CriticalPercolation.Modular.Mass

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

noncomputable def reverseGuess (T : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (s : ℝ) (e : E) : ℝ :=
  (if openPivot F e ω then (1-p)*T.queryDelta F w ω e else 0) /
    (1+s+T.prefixScore p F w ω e)^2

noncomputable def reverseMass (T : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (s : ℝ) : ℝ :=
  match T with
  | .done _ => 0
  | .ask f l r =>
    let b := if openPivot F f ω then (1-p)*delta w F f else 0
    b/(1+s+b)^2 + if ω f then r.reverseMass p F (pin w f True) ω (s+b)
      else l.reverseMass p F (pin w f False) ω (s+b)

lemma reverseMass_eq_sum (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (p : ℝ) (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E) (s : ℝ) :
    T.reverseMass p F w ω s = ∑ e, T.reverseGuess p F w ω s e := by
  induction T generalizing used w s with
  | done _ => simp [reverseMass,reverseGuess,queryDelta,prefixScore]
  | ask f l r hl hr =>
    let b := if openPivot F f ω then (1-p)*delta w F f else 0
    have hsum (T' : SearchTree E R) (w' : E → Prop → ℝ) (hT' : T'.Valid (insert f used)) :
        (∑ e, (if openPivot F e ω then
          (1-p)*(if e = f then delta w F f else T'.queryDelta F w' ω e) else 0) /
          (1+s+(b+if e=f then 0 else T'.prefixScore p F w' ω e))^2) =
        b/(1+s+b)^2 + ∑ e, T'.reverseGuess p F w' ω (s+b) e := by
      have hz := queryDelta_zero_used T' _ hT' F w' ω f (Finset.mem_insert_self _ _)
      have heq (e : E) : (if openPivot F e ω then
          (1-p)*(if e = f then delta w F f else T'.queryDelta F w' ω e) else 0) /
          (1+s+(b+if e=f then 0 else T'.prefixScore p F w' ω e))^2 =
          (if e=f then b/(1+s+b)^2 else 0) + T'.reverseGuess p F w' ω (s+b) e := by
        by_cases he : e=f
        · subst e
          simp [reverseGuess,hz,b]
        · simp only [ite_eq_right he,reverseGuess,zero_add]
          congr 2; ring
      simp only [heq,Finset.sum_add_distrib]
      simp
    rw [reverseMass]
    by_cases hf : ω f
    · simp only [ite_eq_left hf]
      rw [hr _ hT.2.2 (pin w f True),← hsum r (pin w f True) hT.2.2]
      simp only [reverseGuess,queryDelta,prefixScore,ite_eq_left hf]
      rfl
    · simp only [ite_eq_right hf]
      rw [hl _ hT.2.1 (pin w f False),← hsum l (pin w f False) hT.2.1]
      simp only [reverseGuess,queryDelta,prefixScore,ite_eq_right hf]
      rfl

lemma reverseMass_bound (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ a b, a ⊆ b → F a → F b) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ T.reverseMass p F w ω s ∧ T.reverseMass p F w ω s ≤ 1/(1+s) := by
  induction T generalizing used w s with
  | done _ => exact ⟨le_rfl, div_nonneg zero_le_one (by linarith)⟩
  | ask f l r hl hr =>
    let b := if openPivot F f ω then (1-p)*delta w F f else 0
    have hf0 : w f False ≠ 0 := by rw [(hf f hT.1).1]; linarith [hp.2]
    have hf1 : w f True ≠ 0 := by rw [(hf f hT.1).2]; exact hp.1.ne'
    have hb : 0 ≤ b := by
      dsimp [b]
      split_ifs
      · exact mul_nonneg (sub_nonneg.mpr hp.2.le) (delta_unit w hw hn f hf0 hf1 F hF).1
      · exact le_rfl
    have hb' : 0 ≤ b/(1+s+b)^2 := div_nonneg hb (sq_nonneg _)
    have hs' : 0 ≤ s+b := add_nonneg hs hb
    have step {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1/(1+(s+b))) :
        0 ≤ b/(1+s+b)^2+x ∧ b/(1+s+b)^2+x ≤ 1/(1+s) := by
      refine ⟨add_nonneg hb' hx.1, ?_⟩
      calc
        _ ≤ b/(1+s+b)^2 + 1/(1+(s+b)) := add_le_add_right hx.2 _
        _ ≤ _ := by simpa only [add_assoc] using ReverseGuess.step_bound hs hb
    simp only [reverseMass]
    by_cases hbit : ω f
    · simp only [ite_eq_left hbit]
      exact step (hr _ hT.2.2 _ (pin_normalized w hw f True)
        (pin_nonneg w hn f True) (fresh_pin w p used hf f True) hs')
    · simp only [ite_eq_right hbit]
      exact step (hl _ hT.2.1 _ (pin_normalized w hw f False)
        (pin_nonneg w hn f False) (fresh_pin w p used hf f False) hs')

theorem reverseGuess_subprobability (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ a b, a ⊆ b → F a → F b) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) :
    (∀ e, 0 ≤ T.reverseGuess p F w ω 0 e) ∧ (∑ e, T.reverseGuess p F w ω 0 e) ≤ 1 := by
  constructor
  · intro e
    apply div_nonneg _ (sq_nonneg _)
    split_ifs
    · exact mul_nonneg (sub_nonneg.mpr hp.2.le)
        (queryDelta_nonneg T used hT hp F hF w hw hn hf ω e)
    · exact le_rfl
  · rw [← reverseMass_eq_sum T used hT]
    simpa using (reverseMass_bound T used hT hp F hF w hw hn hf ω (s := 0) le_rfl).2

end CriticalPercolation.SearchTree

end
end

end OAI
