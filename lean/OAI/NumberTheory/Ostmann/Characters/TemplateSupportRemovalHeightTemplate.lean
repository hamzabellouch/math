import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalHeightTemplateBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
open SymbolicHistory
variable {ι:Type*}

theorem recursiveExpressions_syntaxSize_bound (k j : ℕ) :
    ∃ C : ℕ,1≤C ∧ ∀ (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
      (t : HistoryReconstruction.Tree j) (M : ℕ),
      (∀i,(e i).syntaxSize≤M) →
      (∀q∈pivotExpressions k j s e t,q.syntaxSize≤C*(M+1)) ∧
      (∀z∈bottomExpressions k j b s e t,∀i,(z.2.2 i).syntaxSize≤C*(M+1)) := by
  induction j with
  | zero =>
    refine ⟨1,by omega,?_⟩
    intro b s e t M h
    constructor
    · simp only [pivotExpressions,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    · intro z hz i
      have hz' : z=(b,s,e) := List.mem_singleton.mp hz
      subst z
      simpa only [one_mul] using (h i).trans (Nat.le_succ M)
  | succ j ih =>
    obtain ⟨C,hC,ih⟩ := ih
    let A := expressionStepFactor k j
    refine ⟨(C+1)*(A+1),by nlinarith,?_⟩
    intro b s e t M h
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hP : P.syntaxSize≤A*(M+1) := pivotExpression_syntaxSize k j e s _ _ M h
    have hchild (v : Bool) :
        ∀i,(childExpressions k j v e P i).syntaxSize≤A*(M+1) :=
      childExpressions_syntaxSize k j v e s _ _ M h
    have hleft := ih b t.1.1 (childExpressions k j true e P) t.2.1 (A*(M+1)) (hchild true)
    have hright := ih (!b) t.1.2 (childExpressions k j false e P) t.2.2 (A*(M+1)) (hchild false)
    have hscale : C*(A*(M+1)+1)≤((C+1)*(A+1))*(M+1) := by nlinarith
    have hPscale : A*(M+1)≤((C+1)*(A+1))*(M+1) := by nlinarith
    constructor
    · intro q hq
      change q∈P::(_++_) at hq
      rcases List.mem_cons.mp hq with hq|hq
      · subst q;exact hP.trans hPscale
      · rcases List.mem_append.mp hq with hq|hq
        · exact (hleft.1 q hq).trans hscale
        · exact (hright.1 q hq).trans hscale
    · intro z hz i
      change z∈(_++_) at hz
      rcases List.mem_append.mp hz with hz|hz
      · exact (hleft.2 z hz i).trans hscale
      · exact (hright.2 z hz i).trans hscale

theorem obstructionExpressions_syntaxSize_bound (k j : ℕ) :
    ∃ C : ℕ,∀ (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
      (t : HistoryReconstruction.Tree j) (M : ℕ),
      (∀i,(e i).syntaxSize≤M) →
      ∀q∈obstructionExpressions k j b s e t,q.syntaxSize≤C*(M+1) := by
  obtain ⟨C,hC,hbound⟩ := recursiveExpressions_syntaxSize_bound (ι:=ι) k j
  let N := Fintype.card (schedule k 0).Slot
  refine ⟨(N+1)*(C+1),?_⟩
  intro b s e t M h q hq
  obtain ⟨hp,hb⟩ := hbound b s e t M h
  rcases List.mem_append.mp hq with hq|hq
  · have hh := hp q hq
    have hscale : C*(M+1)≤((N+1)*(C+1))*(M+1) := by nlinarith
    exact hh.trans hscale
  · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    have hh := finiteProductExpression_syntaxSize z.2.2 (C*(M+1)) (hb z hz)
    change (periodExpression k z.2.2).syntaxSize≤(N+1)*(C*(M+1)+1) at hh
    exact hh.trans (by nlinarith)

end Ostmann.Characters.Template

end

end OAI
