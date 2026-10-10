import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudget
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingModulusBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedBudget
open SymbolicHistory Template TemplateOneSidedCancellation HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable
variable {ι α : Type*}

theorem expressionProduct_denominator (es : List (Expr ι))
    (he : ∀ e ∈ es,e.denominator = 1) :
    (HistoryReconstruction.expressionProduct es).denominator = 1 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [HistoryReconstruction.expressionProduct,Expr.denominator,
      he e List.mem_cons_self,ih (fun q hq => he q (List.mem_cons_of_mem _ hq)),one_mul]

theorem finiteProductExpression_denominator [Fintype α]
    (e : α → Expr ι) (he : ∀ i,(e i).denominator = 1) :
    (finiteProductExpression e).denominator = 1 := by
  apply expressionProduct_denominator
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact he _

theorem survivingSampledExpressions_denominator (k j : ℕ) (width : Role → ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) (i : (schedule k j).Slot) :
    (survivingSampledExpressions k j width P e i).denominator = 1 := by
  apply childExpressions_preserves k j true _ (.fixed P) (fun q => q.denominator = 1)
  · intro z
    cases z with
    | inl z =>
      exact finiteProductExpression_denominator
        (fun a : Fin (width ((schedule k j).role z.1.val)) =>
          Expr.atom (ι:=SurvivingPrimeIndex k j width) (.inl (e ⟨z.1,a⟩))) (fun _ => rfl)
    | inr z =>
      exact finiteProductExpression_denominator
        (fun a : Fin (width ((schedule k j).role z.val)) =>
          Expr.atom (ι:=SurvivingPrimeIndex k j width) (.inr ⟨z,a⟩)) (fun _ => rfl)
  · rfl

theorem sampledExpressions_denominator (k j : ℕ) (width : Role → ℕ)
    (i : (schedule k j).Slot) : (sampledExpressions k j width i).denominator = 1 :=
  finiteProductExpression_denominator _ (fun _ => rfl)

theorem sampledExpressions_supportModulus (k j : ℕ) (width : Role → ℕ)
    (i : (schedule k j).Slot) : (sampledExpressions k j width i).supportModulus = 1 :=
  finiteProductExpression_supportModulus _ (fun _ => rfl)

theorem surviving_residueModulus_eq_sampled (k j : ℕ) (width : Role → ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (s : ℤ) (t : HistoryReconstruction.Tree j) (width' : Role → ℕ) :
    residueModulus (historyResidueGuards k j s (survivingSampledExpressions k j width P e) t) =
      residueModulus (historyResidueGuards k j s (sampledExpressions k j width') t) := by
  apply historyResidueModulus_congr
  intro i
  exact ⟨(survivingSampledExpressions_denominator k j width P e i).trans
      (sampledExpressions_denominator k j width' i).symm,
    (survivingSampledExpressions_supportModulus k j width P e i).trans
      (sampledExpressions_supportModulus k j width' i).symm⟩

theorem surviving_residueModulus_pivot_independent (k j : ℕ) (width : Role → ℕ)
    (P Q : ℤ) (e f : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (s : ℤ) (t : HistoryReconstruction.Tree j) :
    residueModulus (historyResidueGuards k j s (survivingSampledExpressions k j width P e) t) =
      residueModulus (historyResidueGuards k j s (survivingSampledExpressions k j width Q f) t) := by
  rw [surviving_residueModulus_eq_sampled k j width P e s t (fun _ => 0),
    surviving_residueModulus_eq_sampled k j width Q f s t (fun _ => 0)]

theorem surviving_residueModulus_le_cubic_exp {a : ℝ} (ha : 0 ≤ a)
    (k j m : ℕ) (hm : 1 ≤ m) (width : Role → ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (s : ℤ) (t : HistoryReconstruction.Tree j)
    (ht : RangeSupported (ranges a (m:ℝ) j) j [] s t) :
    ((residueModulus (historyResidueGuards k j s
      (survivingSampledExpressions k j width P e) t)).natAbs:ℝ) ≤
      Real.exp (residuePolynomialConstant a k j*(1+(m:ℝ))^3) := by
  rw [surviving_residueModulus_eq_sampled k j width P e s t (fun _ => 0)]
  exact sampled_residueModulus_le_cubic_exp ha k j m hm (fun _ => 0)
    (fun _ => Nat.zero_le _) s t ht

theorem surviving_historyPairResidueModulus_le_cubic_exp {a : ℝ} (ha : 0 ≤ a)
    (k j m : ℕ) (hm : 1 ≤ m) (width : Role → ℕ) (P P' : ℤ)
    (e f : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (s v : ℤ) (t u : HistoryReconstruction.Tree j)
    (ht : RangeSupported (ranges a (m:ℝ) j) j [] s t)
    (hu : RangeSupported (ranges a (m:ℝ) j) j [] v u) :
    (historyPairResidueModulus k j s (survivingSampledExpressions k j width P e) t
      v (survivingSampledExpressions k j width P' f) u:ℝ) ≤
      Real.exp ((2*residuePolynomialConstant a k j)*(1+(m:ℝ))^3) := by
  have h₁ := surviving_residueModulus_le_cubic_exp ha k j m hm width P e s t ht
  have h₂ := surviving_residueModulus_le_cubic_exp ha k j m hm width P' f v u hu
  simp only [historyPairResidueModulus,pairResidueModulus,naturalResidueModulus,Nat.cast_mul]
  calc
    _ ≤ Real.exp (residuePolynomialConstant a k j*(1+(m:ℝ))^3) *
        Real.exp (residuePolynomialConstant a k j*(1+(m:ℝ))^3) :=
      mul_le_mul h₁ h₂ (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

theorem surviving_historyPairResidueModulus_le_historyPolynomialCost {a : ℝ} (ha : 0 ≤ a)
    (k j : ℕ) (z L : ℝ) (hm : 1 ≤ ⌊z*L⌋₊) (width : Role → ℕ) (P P' : ℤ)
    (e f : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (s v : ℤ) (t u : HistoryReconstruction.Tree j)
    (ht : RangeSupported (ranges a (⌊z*L⌋₊:ℝ) j) j [] s t)
    (hu : RangeSupported (ranges a (⌊z*L⌋₊:ℝ) j) j [] v u) :
    (historyPairResidueModulus k j s (survivingSampledExpressions k j width P e) t
      v (survivingSampledExpressions k j width P' f) u:ℝ) ≤
      Real.exp (historyPolynomialCost (2*residuePolynomialConstant a k j) z 3 L) :=
  surviving_historyPairResidueModulus_le_cubic_exp ha k j _ hm width P P' e f s v t u ht hu

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
