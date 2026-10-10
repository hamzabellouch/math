import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetStructure

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedBudget
open SymbolicHistory Template TemplateOneSidedCancellation
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

def guardCountFactor (k : ℕ) : ℕ → ℕ
  | 0 => Fintype.card (schedule k 0).Slot+1
  | j+1 => Fintype.card (schedule k (j+1)).Slot+5+2*guardCountFactor k j

theorem historyGuards_length (k j : ℕ) (B V : ℕ → ℤ)
    (g : (l : ℕ) → ℤ → List (Guard (schedule k l).Slot)) (G : ℕ)
    (hg : ∀l s,(g l s).length ≤ G) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) :
    (historyGuards k B V g j s e t).length ≤ guardCountFactor k j*(G+1) := by
  induction j generalizing s with
  | zero =>
    simp only [historyGuards,List.length_append,List.length_map,positiveGuards,List.length_ofFn,guardCountFactor]
    nlinarith [hg 0 s]
  | succ j ih =>
    have hl := ih t.1.1 (childExpressions k j true e (pivotExpression k j e s t.1.1 t.1.2)) t.2.1
    have hr := ih t.1.2 (childExpressions k j false e (pivotExpression k j e s t.1.1 t.1.2)) t.2.2
    simp only [historyGuards,List.length_append,List.length_map,positiveGuards,List.length_ofFn,
      nodeGuards,List.length_cons,List.length_nil,guardCountFactor]
    nlinarith [hg (j+1) s]

lemma positiveGuards_size (k j : ℕ) (e : Expressions (ι:=ι) k j) (M : ℕ)
    (he : ∀i,(e i).syntaxSize ≤ M) :
    ∀q∈positiveGuards k j e,q.expression.syntaxSize ≤ M := by
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact he _

lemma nodeGuards_size (k j : ℕ) (e : Expressions (ι:=ι) k (j+1))
    (s v w B V : ℤ) (M : ℕ) (he : ∀i,(e i).syntaxSize ≤ M) :
    ∀q∈nodeGuards k j e s v w B V,
      q.expression.syntaxSize ≤ expressionStepFactor k j*(M+1) := by
  have hp := pivotExpression_syntaxSize k j e s v w M he
  have hc := finiteProductExpression_syntaxSize
    (fun i : {i:(schedule k j).Slot // (schedule k j).IsCopied j i}=>e (.inl (i,false))) M (fun _=>he _)
  have hc' : (copiedExpression k j false e).syntaxSize ≤ expressionStepFactor k j*(M+1) := by
    change (copiedExpression k j false e).syntaxSize ≤ _ at hc
    unfold expressionStepFactor
    nlinarith
  intro q hq
  simp only [nodeGuards,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl
  · exact hc'
  · exact hp
  · exact hp
  · exact hc'

theorem historyGuards_size (k j : ℕ) (B V : ℕ → ℤ)
    (g : (l : ℕ) → ℤ → List (Guard (schedule k l).Slot)) (G : ℕ)
    (hg : ∀l s,∀q∈g l s,q.expression.syntaxSize ≤ G)
    (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (M : ℕ) (he : ∀i,(e i).syntaxSize ≤ M) :
    ∀q∈historyGuards k B V g j s e t,
      q.expression.syntaxSize ≤ recursiveSizeFactor k j*(G+1)*(M+1) := by
  induction j generalizing s M with
  | zero =>
    intro q hq
    rcases List.mem_append.mp hq with hq|hq
    · have hh := positiveGuards_size k 0 e M he q hq
      simp only [recursiveSizeFactor,one_mul]
      nlinarith
    · obtain ⟨q0,hq0,rfl⟩ := List.mem_map.mp hq
      have hh := substitute_syntaxSize e q0.expression M he
      have hh' := hg 0 s q0 hq0
      change (substitute e q0.expression).syntaxSize ≤ _
      simp only [recursiveSizeFactor,one_mul]
      nlinarith
  | succ j ih =>
    let A := expressionStepFactor k j
    let C := recursiveSizeFactor k j
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hc (v : Bool) : ∀i,(childExpressions k j v e P i).syntaxSize ≤ A*(M+1) :=
      childExpressions_syntaxSize k j v e s _ _ M he
    have hl := ih t.1.1 (childExpressions k j true e P) t.2.1 (A*(M+1)) (hc true)
    have hr := ih t.1.2 (childExpressions k j false e P) t.2.2 (A*(M+1)) (hc false)
    have hscale : C*(A*(M+1)+1) ≤ ((C+1)*(A+1))*(M+1) := by nlinarith
    have hscale' : C*(G+1)*(A*(M+1)+1) ≤ ((C+1)*(A+1))*(G+1)*(M+1) := by
      nlinarith [Nat.mul_le_mul_left (G+1) hscale]
    have hlarge : (G+1)*(M+1) ≤ recursiveSizeFactor k (j+1)*(G+1)*(M+1) := by
      have hp : 1 ≤ recursiveSizeFactor k (j+1) := recursiveSizeFactor_pos k (j+1)
      simpa only [one_mul,mul_assoc] using Nat.mul_le_mul_right ((G+1)*(M+1)) hp
    have hnode : A*(M+1) ≤ recursiveSizeFactor k (j+1)*(G+1)*(M+1) := by
      change A*(M+1) ≤ ((C+1)*(A+1))*(G+1)*(M+1)
      have ha : A ≤ (C+1)*(A+1) := by nlinarith
      have hg' := Nat.mul_le_mul_left ((C+1)*(A+1)) (show 1 ≤ G+1 by omega)
      simp only [mul_one] at hg'
      exact Nat.mul_le_mul_right (M+1) (ha.trans hg')
    intro q hq
    change q∈positiveGuards _ _ _ ++ (_ ++ (_ ++ (_ ++ _))) at hq
    rcases List.mem_append.mp hq with hq|hq
    · have hh := positiveGuards_size k (j+1) e M he q hq
      apply le_trans hh
      nlinarith
    · rcases List.mem_append.mp hq with hq|hq
      · obtain ⟨q0,hq0,rfl⟩ := List.mem_map.mp hq
        have hh := substitute_syntaxSize e q0.expression M he
        have hh' := hg (j+1) s q0 hq0
        change (substitute e q0.expression).syntaxSize ≤ _
        apply le_trans _ hlarge
        nlinarith
      · rcases List.mem_append.mp hq with hq|hq
        · exact (nodeGuards_size k j e s _ _ _ _ M he q hq).trans hnode
        · rcases List.mem_append.mp hq with hq|hq
          · exact (hl q hq).trans hscale'
          · exact (hr q hq).trans hscale'

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
