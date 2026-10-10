import OAI.NumberTheory.Ostmann.Characters.SourceTemplateDefs
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingExpressions

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedBudget
open SymbolicHistory Template HigherBiasSource HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable

def survivingSourceWidthBudget {k : ℕ} (cfg : SourceConfiguration k) : ℕ :=
  1 + ∑ i : Fin (k+1),(cfg.2 i).length

theorem sourceWidth_le_surviving_budget {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (r : Role) : sourceWidth cfg m r ≤ survivingSourceWidthBudget cfg*(m+1) := by
  have hlen (i : Fin (k+1)) : (cfg.2 i).length ≤ ∑ i : Fin (k+1),(cfg.2 i).length :=
    Finset.single_le_sum (f:=fun i : Fin (k+1) => (cfg.2 i).length)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
  cases r with
  | word => simp only [sourceWidth,survivingSourceWidthBudget,Nat.add_mul,one_mul]; omega
  | pivot r =>
    simp only [sourceWidth]
    split_ifs with hr
    · have hh := hlen ⟨r,by omega⟩
      simp only [survivingSourceWidthBudget]
      nlinarith
    · exact Nat.zero_le _
  | anchor r b => simp only [sourceWidth,survivingSourceWidthBudget,Nat.add_mul,one_mul]; omega
  | filler =>
    have hh := hlen (Fin.last k)
    simp only [sourceWidth,survivingSourceWidthBudget]
    nlinarith

def survivingSourceSyntaxConstant {k : ℕ} (cfg : SourceConfiguration k) : ℕ :=
  2*(survivingSourceWidthBudget cfg+1)

theorem survivingSampledExpressions_source_syntaxSize {k : ℕ}
    (cfg : SourceConfiguration k) (m j : ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (i : (schedule k j).Slot) :
    (survivingSampledExpressions k j (sourceWidth cfg m) P e i).syntaxSize ≤
      survivingSourceSyntaxConstant cfg*(m+1) :=
  survivingSampledExpressions_syntaxSize_linear k j (sourceWidth cfg m) P e
    (survivingSourceWidthBudget cfg) m (sourceWidth_le_surviving_budget cfg m) i

theorem survivingCopied_card_le {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :
    Fintype.card (CopiedConstituent (schedule k j) j (sourceWidth cfg m)) ≤
      Fintype.card {i : (schedule k j).Slot // (schedule k j).IsCopied j i} *
        survivingSourceWidthBudget cfg*(m+1) := by
  change Fintype.card (Σ i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i},
    Fin (sourceWidth cfg m ((schedule k j).role i.val))) ≤ _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∑ _i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i},
        survivingSourceWidthBudget cfg*(m+1) :=
      Finset.sum_le_sum (fun i _ => sourceWidth_le_surviving_budget cfg m _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,Nat.mul_assoc]

def survivingCopiedSyntaxConstant {k : ℕ} (cfg : SourceConfiguration k) (j : ℕ) : ℕ :=
  2*(Fintype.card {i : (schedule k j).Slot // (schedule k j).IsCopied j i}*
    survivingSourceWidthBudget cfg+1)

theorem survivingCopiedProductExpression_source_syntaxSize {k : ℕ}
    (cfg : SourceConfiguration k) (m j : ℕ) :
    (survivingCopiedProductExpression k j (sourceWidth cfg m)).syntaxSize ≤
      survivingCopiedSyntaxConstant cfg j*(m+1) := by
  apply (survivingCopiedProductExpression_syntaxSize k j (sourceWidth cfg m)).trans
  have hh := survivingCopied_card_le cfg m j
  unfold survivingCopiedSyntaxConstant
  nlinarith

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
