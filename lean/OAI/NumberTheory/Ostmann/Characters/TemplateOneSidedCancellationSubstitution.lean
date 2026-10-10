import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationGuards

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory
variable {ι κ : Type*}

def substitute (x : κ → Expr ι) : Expr κ → Expr ι
  | .atom i => x i
  | .fixed c => .fixed c
  | .add a b => .add (substitute x a) (substitute x b)
  | .sub a b => .sub (substitute x a) (substitute x b)
  | .mul a b => .mul (substitute x a) (substitute x b)
  | .divide a d => .divide (substitute x a) d

theorem substitute_eval (x : κ → Expr ι) (e : Expr κ) (a : ι → ℤ) :
    (substitute x e).integerEval a=e.integerEval (fun i => (x i).integerEval a) := by
  induction e <;> simp_all [substitute,Expr.integerEval]

theorem substitute_valid (x : κ → Expr ι) (e : Expr κ)
    (hx : ∀ i, (x i).Valid) (he : e.Valid) : (substitute x e).Valid := by
  induction e <;> simp_all [substitute,Expr.Valid]

theorem substitute_integral (x : κ → Expr ι) (e : Expr κ) (a : ι → ℤ)
    (hx : ∀ i, (x i).IntegralAt a)
    (he : e.IntegralAt (fun i => (x i).integerEval a)) :
    (substitute x e).IntegralAt a := by
  induction e <;> simp_all [substitute,Expr.IntegralAt,substitute_eval]

def Guard.substitute (g : Guard κ) (x : κ → Expr ι) : Guard ι :=
  ⟨TemplateOneSidedCancellation.substitute x g.expression,g.threshold,g.above,g.strict⟩

theorem Guard.substitute_holds (g : Guard κ) (x : κ → Expr ι) (a : ι → ℤ) :
    (g.substitute x).holds a ↔ g.holds (fun i => (x i).integerEval a) := by
  simp only [Guard.holds,Guard.substitute,substitute_eval]

def guardsHold (g : List (Guard ι)) (a : ι → ℤ) : Prop := ∀ q ∈ g, q.holds a

theorem guardsHold_append (g h : List (Guard ι)) (a : ι → ℤ) :
    guardsHold (g++h) a ↔ guardsHold g a ∧ guardsHold h a := by
  constructor
  · intro h
    exact ⟨fun q hq => h q (List.mem_append_left _ hq),fun q hq => h q (List.mem_append_right _ hq)⟩
  · rintro ⟨hg,hh⟩ q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hg q hq
    · exact hh q hq

theorem guardsHold_substitute (g : List (Guard κ)) (x : κ → Expr ι) (a : ι → ℤ) :
    guardsHold (g.map (fun q => q.substitute x)) a ↔
      guardsHold g (fun i => (x i).integerEval a) := by
  simp only [guardsHold,List.forall_mem_map,Guard.substitute_holds]

def canonicalMask (k : ℕ)
    (g : (j : ℕ) → ℤ → List (Guard (Template.schedule k j).Slot)) :
    (j : ℕ) → ℤ → Template.State k j → Prop := fun j s x => guardsHold (g j s) x

def maskGuards (k : ℕ)
    (g : (j : ℕ) → ℤ → List (Guard (Template.schedule k j).Slot)) :
    (j : ℕ) → ℤ → Template.Expressions (ι:=ι) k j →
      HistoryReconstruction.Tree j → List (Guard ι)
  | 0,s,e,_ => (g 0 s).map (fun q => q.substitute e)
  | j+1,s,e,t =>
      let P := Template.pivotExpression k j e s t.1.1 t.1.2
      (g (j+1) s).map (fun q => q.substitute e) ++
      (maskGuards k g j t.1.1 (Template.childExpressions k j true e P) t.2.1 ++
        maskGuards k g j t.1.2 (Template.childExpressions k j false e P) t.2.2)

def masksOnHistory (k : ℕ)
    (g : (j : ℕ) → ℤ → List (Guard (Template.schedule k j).Slot)) :
    (j : ℕ) → ℤ → Template.State k j → HistoryReconstruction.Tree j → Prop
  | 0,s,x,_ => canonicalMask k g 0 s x
  | j+1,s,x,t => canonicalMask k g (j+1) s x ∧
      masksOnHistory k g j t.1.1
        (Template.childState k j true x (Template.reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ∧
      masksOnHistory k g j t.1.2
        (Template.childState k j false x (Template.reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

theorem maskGuards_holds (k : ℕ)
    (g : (j : ℕ) → ℤ → List (Guard (Template.schedule k j).Slot))
    (j : ℕ) (s : ℤ) (e : Template.Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    guardsHold (maskGuards k g j s e t) a ↔
      masksOnHistory k g j s (Template.evalExpressions a e) t := by
  induction j generalizing s with
  | zero => exact guardsHold_substitute (g 0 s) e a
  | succ j ih =>
    simp only [maskGuards,masksOnHistory,guardsHold_append,guardsHold_substitute,ih,
      Template.childExpressions_eval,Template.pivotExpression_eval,canonicalMask]
    rfl

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
