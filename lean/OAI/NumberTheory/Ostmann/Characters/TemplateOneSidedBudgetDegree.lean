import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetGuards
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationVariation
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalCardinality

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedBudget
open SymbolicHistory Template TemplateOneSidedCancellation
attribute [local instance] Classical.propDecidable
variable {ι σ τ : Type*} [DecidableEq ι] [Fintype σ] [Fintype τ]

omit [DecidableEq ι] in
theorem leafDegreeBudget_le (k : ℕ) (g : σ → Guard ι)
    (leaf : τ → BottomExpression (ι:=ι) k) (X A B : ℝ) (D : ℕ)
    (hg : ∀s,(g s).expression.syntaxSize ≤ D)
    (hl : ∀t,(periodExpression k (leaf t).2.2).syntaxSize ≤ D) :
    leafDegreeBudget k g leaf X A B ≤ 2*(Fintype.card σ+3*Fintype.card τ)*D+1 := by
  have hp : ∀s,(profileGuards g (fun t=>periodExpression k (leaf t).2.2) X A B s).expression.degreeBudget ≤ D := by
    intro s
    rcases s with s|⟨t,b⟩
    · exact (g s).expression.degreeBudget_le_syntaxSize.trans (hg s)
    · cases b <;> exact (periodExpression k (leaf t).2.2).degreeBudget_le_syntaxSize.trans (hl t)
  have hsum := Finset.sum_le_sum (fun s (_ : s∈Finset.univ)=>hp s)
  have hleaf := Finset.sum_le_sum (fun t (_ : t∈Finset.univ)=>
    (periodExpression k (leaf t).2.2).degreeBudget_le_syntaxSize.trans (hl t))
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Fintype.card_sum,
    Fintype.card_prod,Fintype.card_bool] at hsum hleaf
  unfold leafDegreeBudget
  nlinarith

theorem leafData_degreeCost_size (k : ℕ) (g : σ → Guard ι)
    (leaf : τ → BottomExpression (ι:=ι) k) (i : ι)
    (x : TemplateSupportRemoval.Other i → ℤ) (X A B : ℝ) (D : ℕ)
    (hg : ∀s,(g s).expression.syntaxSize ≤ D)
    (hl : ∀t,(periodExpression k (leaf t).2.2).syntaxSize ≤ D) :
    (leafData k g leaf i x X A B).degreeCost ≤ 2*(Fintype.card σ+3*Fintype.card τ)*D+1 :=
  (leafData_degreeCost_le k g leaf i x X A B).trans
    (leafDegreeBudget_le k g leaf X A B D hg hl)

theorem canonical_leafData_degreeCost (k j : ℕ) (B0 V0 : ℕ → ℤ)
    (g : (l : ℕ) → ℤ → List (Guard (schedule k l).Slot)) (Gcount Gsize : ℕ)
    (hc : ∀l s,(g l s).length ≤ Gcount)
    (hg : ∀l s,∀q∈g l s,q.expression.syntaxSize ≤ Gsize)
    (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (M : ℕ) (he : ∀i,(e i).syntaxSize ≤ M) (i : ι)
    (x : TemplateSupportRemoval.Other i → ℤ) (X A B : ℝ) :
    (leafData k
      (fun q : Fin (historyGuards k B0 V0 g j s e t).length=>
        (historyGuards k B0 V0 g j s e t).get q)
      (fun q : Fin (bottomExpressions k j b s e t).length=>
        (bottomExpressions k j b s e t).get q) i x X A B).degreeCost ≤
      2*(guardCountFactor k j*(Gcount+1)+3*2^j)*
        ((recursiveSizeFactor k j*(Gsize+1)+obstructionSizeFactor k j)*(M+1))+1 := by
  let D := (recursiveSizeFactor k j*(Gsize+1)+obstructionSizeFactor k j)*(M+1)
  have hguards : ∀q : Fin (historyGuards k B0 V0 g j s e t).length,
      ((historyGuards k B0 V0 g j s e t).get q).expression.syntaxSize ≤ D := by
    intro q
    have hh := historyGuards_size k j B0 V0 g Gsize hg s e t M he _ (List.get_mem _ q)
    dsimp only [D]
    nlinarith
  have hleaves : ∀q : Fin (bottomExpressions k j b s e t).length,
      (periodExpression k ((bottomExpressions k j b s e t).get q).2.2).syntaxSize ≤ D := by
    intro q
    have hm : periodExpression k ((bottomExpressions k j b s e t).get q).2.2 ∈
        obstructionExpressions k j b s e t := by
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_,List.get_mem _ q,rfl⟩)
    have hh := obstructionExpressions_size k j b s e t M he _ hm
    have hp : obstructionSizeFactor k j ≤ recursiveSizeFactor k j*(Gsize+1)+obstructionSizeFactor k j := by omega
    exact hh.trans (Nat.mul_le_mul_right (M+1) hp)
  have hh := leafData_degreeCost_size k _ _ i x X A B D hguards hleaves
  simp only [Fintype.card_fin] at hh
  have hcount := historyGuards_length k j B0 V0 g Gcount hc s e t
  apply hh.trans
  rw [bottomExpressions_length k j b s e t]
  change 2*((historyGuards k B0 V0 g j s e t).length+3*2^j)*D+1 ≤ _
  change _ ≤ 2*(guardCountFactor k j*(Gcount+1)+3*2^j)*D+1
  gcongr

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
