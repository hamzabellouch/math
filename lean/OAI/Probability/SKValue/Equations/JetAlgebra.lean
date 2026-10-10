import Mathlib

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

inductive JetExpr where
  | const : ℝ → JetExpr
  | coord : ℕ → JetExpr
  | add : JetExpr → JetExpr → JetExpr
  | mul : JetExpr → JetExpr → JetExpr

namespace JetExpr
noncomputable def eval (R : ℕ → ℝ) : JetExpr → ℝ
  | const c => c
  | coord j => R j
  | add e f => eval R e+eval R f
  | mul e f => eval R e*eval R f

noncomputable def D (σ : ℕ → JetExpr) : JetExpr → JetExpr
  | const _ => const 0
  | coord j => σ j
  | add e f => add (D σ e) (D σ f)
  | mul e f => add (mul (D σ e) f) (mul e (D σ f))

lemma hasDerivAt_eval {R : ℕ → ℝ → ℝ} {σ : ℕ → JetExpr} {x : ℝ}
    (hR : ∀ j, HasDerivAt (R j) (eval (fun i ↦ R i x) (σ j)) x) (e : JetExpr) :
    HasDerivAt (fun y ↦ eval (fun i ↦ R i y) e) (eval (fun i ↦ R i x) (D σ e)) x := by
  induction e with
  | const c => exact hasDerivAt_const x c
  | coord j => exact hR j
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

lemma continuous_eval {α : Type*} [TopologicalSpace α] {R : ℕ → α → ℝ}
    (hR : ∀ j, Continuous (R j)) (e : JetExpr) :
    Continuous (fun a ↦ eval (fun j ↦ R j a) e) := by
  induction e with
  | const c => exact continuous_const
  | coord j => exact hR j
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

lemma uniform_bound {α : Type*} {R : ℕ → α → ℝ}
    (hR : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ a, |R j a|≤C) (e : JetExpr) :
    ∃ C : ℝ, 0≤C ∧ ∀ a, |eval (fun j ↦ R j a) e|≤C := by
  induction e with
  | const c => exact ⟨|c|,abs_nonneg c,fun _ ↦ le_rfl⟩
  | coord j => exact hR j
  | add e f he hf =>
    obtain ⟨A,hA,he⟩ := he
    obtain ⟨B,hB,hf⟩ := hf
    exact ⟨A+B,add_nonneg hA hB,fun a ↦ (abs_add_le _ _).trans (add_le_add (he a) (hf a))⟩
  | mul e f he hf =>
    obtain ⟨A,hA,he⟩ := he
    obtain ⟨B,hB,hf⟩ := hf
    exact ⟨A*B,mul_nonneg hA hB,fun a ↦ by
      simpa only [eval,abs_mul] using mul_le_mul (he a) (hf a) (abs_nonneg _) hA⟩

noncomputable def σx (j : ℕ) : JetExpr :=
  add (coord (j+1)) (mul (const (-1)) (mul (coord j) (coord 1)))

noncomputable def σh (j : ℕ) : JetExpr :=
  mul (const (1/2)) (add (coord (j+2)) (mul (const (-1)) (mul (coord j) (coord 2))))

noncomputable def logGradientJet : ℕ → JetExpr
  | 0 => coord 1
  | n+1 => D σx (logGradientJet n)

lemma eval_σx (R : ℕ → ℝ) (j : ℕ) : eval R (σx j)=R (j+1)-R j*R 1 := by
  simp only [σx,eval]; ring
lemma eval_σh (R : ℕ → ℝ) (j : ℕ) : eval R (σh j)=(1/2 : ℝ)*(R (j+2)-R j*R 2) := by
  simp only [σh,eval]; ring

lemma iteratedDeriv_logGradientJet {R : ℕ → ℝ → ℝ}
    (hs : ∀ j, ContDiff ℝ ∞ (R j))
    (hd : ∀ j, deriv (R j)=fun x ↦ R (j+1) x-R j x*R 1 x) (n : ℕ) :
    iteratedDeriv n (R 1)=fun x ↦ eval (fun j ↦ R j x) (logGradientJet n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    apply HasDerivAt.deriv
    apply hasDerivAt_eval
    intro j
    have hj := (((hs j).differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0))) x).hasDerivAt
    simpa only [hd,eval_σx] using hj

end JetExpr
end SKValue

end

end OAI
