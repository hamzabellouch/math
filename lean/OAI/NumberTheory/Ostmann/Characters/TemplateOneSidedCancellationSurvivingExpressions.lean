import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingExpressionsBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedBudget
open SymbolicHistory Template
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

theorem expressionProduct_supportModulus (es : List (Expr ι))
    (he : ∀ e ∈ es,e.supportModulus = 1) :
    (HistoryReconstruction.expressionProduct es).supportModulus = 1 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [HistoryReconstruction.expressionProduct,Expr.supportModulus,
      he e List.mem_cons_self,ih (fun q hq => he q (List.mem_cons_of_mem _ hq)),one_mul]

theorem finiteProductExpression_supportModulus {α : Type*} [Fintype α]
    (e : α → Expr ι) (he : ∀ i,(e i).supportModulus = 1) :
    (finiteProductExpression e).supportModulus = 1 := by
  apply expressionProduct_supportModulus
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact he _

theorem survivingSampledExpressions_supportModulus (k j : ℕ) (width : Role → ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) (i : (schedule k j).Slot) :
    (survivingSampledExpressions k j width P e i).supportModulus = 1 := by
  apply childExpressions_preserves k j true _ (.fixed P) (fun q => q.supportModulus = 1)
  · intro z
    cases z with
    | inl z =>
      exact finiteProductExpression_supportModulus
        (fun a : Fin (width ((schedule k j).role z.1.val)) =>
          Expr.atom (ι:=SurvivingPrimeIndex k j width) (.inl (e ⟨z.1,a⟩))) (fun _ => rfl)
    | inr z =>
      exact finiteProductExpression_supportModulus
        (fun a : Fin (width ((schedule k j).role z.val)) =>
          Expr.atom (ι:=SurvivingPrimeIndex k j width) (.inr ⟨z,a⟩)) (fun _ => rfl)
  · rfl

theorem survivingSampledExpressions_fixedBound (k j : ℕ) (width : Role → ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) {B : ℝ}
    (hB : 1 ≤ B) (hP : |(P:ℝ)| ≤ B) (i : (schedule k j).Slot) :
    (survivingSampledExpressions k j width P e i).FixedBound B := by
  apply childExpressions_preserves k j true _ (.fixed P) (fun q => q.FixedBound B)
  · intro z
    cases z with
    | inl z =>
      exact finiteProductExpression_fixedBound
        (fun a : Fin (width ((schedule k j).role z.1.val)) =>
          Expr.atom (ι:=SurvivingPrimeIndex k j width) (.inl (e ⟨z.1,a⟩))) hB (fun _ => trivial)
    | inr z =>
      exact finiteProductExpression_fixedBound
        (fun a : Fin (width ((schedule k j).role z.val)) =>
          Expr.atom (ι:=SurvivingPrimeIndex k j width) (.inr ⟨z,a⟩)) hB (fun _ => trivial)
  · exact hP

theorem survivingSampledExpressions_fixedLogBound (k j : ℕ) (width : Role → ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) {H : ℝ}
    (hH : 0 ≤ H) (hP : |(P:ℝ)| ≤ Real.exp H) (i : (schedule k j).Slot) :
    (survivingSampledExpressions k j width P e i).FixedLogBound H :=
  survivingSampledExpressions_fixedBound k j width P e (Real.one_le_exp_iff.mpr hH) hP i

theorem survivingSampledExpressions_fixedLogBound_pnat (k j : ℕ) (width : Role → ℕ) (P : ℕ+)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) {H : ℝ}
    (hP : (P:ℝ) ≤ Real.exp H) (i : (schedule k j).Slot) :
    (survivingSampledExpressions k j width P e i).FixedLogBound H := by
  have h1 : (1:ℝ) ≤ P := by exact_mod_cast P.pos
  apply survivingSampledExpressions_fixedBound k j width P e (h1.trans hP)
  simpa only [Int.cast_natCast,abs_of_nonneg (show (0:ℝ) ≤ P from by positivity)] using hP

theorem survivingSampledExpressions_syntaxSize (k j : ℕ) (width : Role → ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) (M : ℕ)
    (hM : ∀ r,width r ≤ M) (i : (schedule k j).Slot) :
    (survivingSampledExpressions k j width P e i).syntaxSize ≤ 2*(M+1) := by
  apply childExpressions_preserves k j true _ (.fixed P) (fun q => q.syntaxSize ≤ 2*(M+1))
  · intro z
    cases z with
    | inl z =>
      have hh := finiteProductExpression_syntaxSize
        (fun a : Fin (width ((schedule k j).role z.1.val)) =>
          Expr.atom (ι:=SurvivingPrimeIndex k j width) (.inl (e ⟨z.1,a⟩))) 1 (fun _ => le_rfl)
      simp only [Fintype.card_fin] at hh
      exact hh.trans (by nlinarith [hM ((schedule k j).role z.1.val)])
    | inr z =>
      have hh := finiteProductExpression_syntaxSize
        (fun a : Fin (width ((schedule k j).role z.val)) =>
          Expr.atom (ι:=SurvivingPrimeIndex k j width) (.inr ⟨z,a⟩)) 1 (fun _ => le_rfl)
      simp only [Fintype.card_fin] at hh
      exact hh.trans (by nlinarith [hM ((schedule k j).role z.val)])
  · change 1 ≤ 2*(M+1)
    omega

theorem survivingSampledExpressions_syntaxSize_linear (k j : ℕ) (width : Role → ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) (C m : ℕ)
    (hM : ∀ r,width r ≤ C*(m+1)) (i : (schedule k j).Slot) :
    (survivingSampledExpressions k j width P e i).syntaxSize ≤ 2*(C+1)*(m+1) :=
  (survivingSampledExpressions_syntaxSize k j width P e _ hM i).trans (by nlinarith)

theorem survivingCopiedProductExpression_supportModulus (k j : ℕ) (width : Role → ℕ) :
    (survivingCopiedProductExpression k j width).supportModulus = 1 :=
  finiteProductExpression_supportModulus _ (fun _ => rfl)

theorem survivingCopiedProductExpression_fixedLogBound (k j : ℕ) (width : Role → ℕ)
    {H : ℝ} (hH : 0 ≤ H) :
    (survivingCopiedProductExpression k j width).FixedLogBound H :=
  finiteProductExpression_fixedBound _ (Real.one_le_exp_iff.mpr hH) (fun _ => trivial)

theorem survivingCopiedProductExpression_syntaxSize (k j : ℕ) (width : Role → ℕ) :
    (survivingCopiedProductExpression k j width).syntaxSize ≤
      2*(Fintype.card (CopiedConstituent (schedule k j) j width)+1) := by
  have hh := finiteProductExpression_syntaxSize
    (fun i : CopiedConstituent (schedule k j) j width =>
      Expr.atom (ι:=SurvivingPrimeIndex k j width) (.inl i)) 1 (fun _ => le_rfl)
  simpa only [survivingCopiedProductExpression,show 1+1=2 by rfl,Nat.mul_comm] using hh

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
