import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSupport
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationNodes

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template
variable {ι : Type*}

structure CurrentArithmetic (k j : ℕ) (s : ℤ) (x : State k j) : Prop where
  root_ne_zero : s ≠ 0
  pairwise : Pairwise (fun i h => IsCoprime (x i) (x h))
  root_coprime : ∀ i, IsCoprime s (x i)

theorem currentAtomSupport_iff (k j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (a : ι → ℤ) :
    CurrentAtomSupport k j s (evalExpressions a e) ↔
      CurrentArithmetic k j s (evalExpressions a e) ∧ guardsHold (positiveGuards k j e) a := by
  rw [positiveGuards_holds]
  constructor
  · intro h
    exact ⟨⟨h.root_ne_zero,h.pairwise,h.root_coprime⟩,h.positive⟩
  · rintro ⟨h,hp⟩
    exact ⟨h.root_ne_zero,hp,h.pairwise,h.root_coprime⟩

def historyArithmetic (k : ℕ) (B V : ℕ → ℤ) :
    (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop
  | 0,s,x,_ => CurrentArithmetic k 0 s x
  | j+1,s,x,t => CurrentArithmetic k (j+1) s x ∧
      NodeArithmetic k j x s t.1.1 t.1.2 (V j) ∧
      IntegerNodeSupport k j s t.1.1 t.1.2 x ∧
      historyArithmetic k B V j t.1.1
        (childState k j true x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ∧
      historyArithmetic k B V j t.1.2
        (childState k j false x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

def historyGuards (k : ℕ) (B V : ℕ → ℤ)
    (g : (j : ℕ) → ℤ → List (Guard (schedule k j).Slot)) :
    (j : ℕ) → ℤ → Expressions (ι:=ι) k j → HistoryReconstruction.Tree j → List (Guard ι)
  | 0,s,e,_ => positiveGuards k 0 e ++ (g 0 s).map (fun q => q.substitute e)
  | j+1,s,e,t =>
      let P := pivotExpression k j e s t.1.1 t.1.2
      positiveGuards k (j+1) e ++
      ((g (j+1) s).map (fun q => q.substitute e) ++
      (nodeGuards k j e s t.1.1 t.1.2 (B j) (V j) ++
      (historyGuards k B V g j t.1.1 (childExpressions k j true e P) t.2.1 ++
        historyGuards k B V g j t.1.2 (childExpressions k j false e P) t.2.2)))

theorem canonicalTransfer_iff (k : ℕ) (B V : ℕ → ℤ)
    (g : (j : ℕ) → ℤ → List (Guard (schedule k j).Slot)) (j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    TransferSupport k (fun j _ => B j) (fun j _ => V j)
      (fun j s x _ => canonicalMask k g j s x) j s (evalExpressions a e) t ↔
      historyArithmetic k B V j s (evalExpressions a e) t ∧
        guardsHold (historyGuards k B V g j s e t) a := by
  induction j generalizing s with
  | zero =>
    simp only [TransferSupport,historyArithmetic,historyGuards,guardsHold_append,
      guardsHold_substitute,canonicalMask]
    rw [currentAtomSupport_iff]
    tauto
  | succ j ih =>
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hl := ih t.1.1 (childExpressions k j true e P) t.2.1
    have hr := ih t.1.2 (childExpressions k j false e P) t.2.2
    simp only [childExpressions_eval,pivotExpression_eval,P,canonicalMask] at hl hr
    simp only [TransferSupport,historyArithmetic,historyGuards,guardsHold_append,
      guardsHold_substitute,canonicalMask]
    rw [currentAtomSupport_iff,nodeSupported_iff,hl,hr]
    tauto

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
