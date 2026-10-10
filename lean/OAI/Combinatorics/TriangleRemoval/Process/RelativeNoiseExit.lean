import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.RelativeCopyNoiseFirst

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def RelativeNoiseExit {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L s : ℕ → ℝ) (B r : ℝ)
    (T : ℕ) (ω : History (Graph n) T) : Prop :=
  ∃ j ≤ T, pastRelativeCopyLoadsSafe required L T j ω ∧
    (∀ k < j, copyCount required (ω (historyIndex T k)) ≤ B*s k) ∧
    r ≤ |historyNoise (fun _ => step) (fun k H => copyCount required H/s k) T j ω|

open Classical in

theorem simultaneous_relative_template_tail {n : ℕ} {I : Type*} [Fintype I]
    {α : I → Type*} [∀ i, Fintype (α i)]
    (required : ∀ i, α i → Graph n) (G : Graph n) (T : ℕ)
    (L s : I → ℕ → ℝ) (c B r : I → ℝ)
    (hc : ∀ i, 0 < c i) (hB : ∀ i, 0 ≤ B i)
    (hs : ∀ i k, k ≤ T → 0 < s i k)
    (hdec : ∀ i k, k < T → s i (k+1) ≤ s i k)
    (hL : ∀ i k, k < T → 0 ≤ L i k)
    (hjump : ∀ i k, k < T → 3*L i k/s i (k+1) ≤ c i)
    (hr : ∀ i, 0 < r i) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ i, RelativeNoiseExit (required i) (L i) (s i) (B i) (r i) T ω
        then 1 else 0) ≤
      ∑ i, 2*(T+1 : ℝ)*Real.exp
        (-(r i)^2/(4*(c i*(copyCount (required i) G/s i 0+
          B i*relativeScaleBudget (s i) T+r i+c i)+c i*r i))) := by
  classical
  have hh := pmfMean_event_union (historyLaw (PMF.pure G) (fun _ => step) T T)
    (Finset.univ : Finset I)
    (fun i ω => RelativeNoiseExit (required i) (L i) (s i) (B i) (r i) T ω)
  simp only [Finset.mem_univ,true_and] at hh
  apply hh.trans
  apply Finset.sum_le_sum
  intro i _
  have ht := triangle_relative_template_self_bounded_tail (required i) G T (L i) (s i)
    (c i) (B i) (hc i) (hB i) (hs i) (hdec i) (hL i) (hjump i) (r i) (hr i)
  convert ht using 1
  apply congrArg (pmfMean _)
  funext ω
  simp only [RelativeNoiseExit]
  congr 1

open Classical in

theorem simultaneous_relative_template_common_tail {n : ℕ} {I : Type*} [Fintype I]
    {α : I → Type*} [∀ i, Fintype (α i)]
    (required : ∀ i, α i → Graph n) (G : Graph n) (T : ℕ)
    (L s : I → ℕ → ℝ) (c B r : I → ℝ)
    (hc : ∀ i, 0 < c i) (hB : ∀ i, 0 ≤ B i)
    (hs : ∀ i k, k ≤ T → 0 < s i k)
    (hdec : ∀ i k, k < T → s i (k+1) ≤ s i k)
    (hL : ∀ i k, k < T → 0 ≤ L i k)
    (hjump : ∀ i k, k < T → 3*L i k/s i (k+1) ≤ c i)
    (hr : ∀ i, 0 < r i) (A : ℝ)
    (hbudget : ∀ i, A ≤ (r i)^2/(4*(c i*(copyCount (required i) G/s i 0+
      B i*relativeScaleBudget (s i) T+r i+c i)+c i*r i))) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ i, RelativeNoiseExit (required i) (L i) (s i) (B i) (r i) T ω
        then 1 else 0) ≤
      (Fintype.card I : ℝ)*2*(T+1)*Real.exp (-A) := by
  apply (simultaneous_relative_template_tail required G T L s c B r hc hB hs hdec hL hjump hr).trans
  calc
    _ ≤ ∑ _i : I, 2*(T+1 : ℝ)*Real.exp (-A) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      exact neg_le_neg (hbudget i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end SharpTerminalLeave

end

end OAI
