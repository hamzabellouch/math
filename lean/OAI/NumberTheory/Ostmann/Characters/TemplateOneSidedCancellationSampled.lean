import OAI.NumberTheory.Ostmann.Characters.TemplateCompositePivotSupportActual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationCanonical

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template
variable {ι κ : Type*}

structure CurrentRootArithmetic (k j : ℕ) (s : ℤ) (x : State k j) : Prop where
  root_ne_zero : s ≠ 0
  root_coprime : ∀ i, IsCoprime s (x i)

theorem currentRootSupport_iff (k j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (a : ι → ℤ) :
    CurrentRootSupport k j s (evalExpressions a e) ↔
      CurrentRootArithmetic k j s (evalExpressions a e) ∧
        guardsHold (positiveGuards k j e) a := by
  rw [positiveGuards_holds]
  constructor
  · intro h
    exact ⟨⟨h.root_ne_zero,h.root_coprime⟩,h.positive⟩
  · rintro ⟨h,hp⟩
    exact ⟨h.root_ne_zero,hp,h.root_coprime⟩

def sampledHistoryArithmetic (k : ℕ) (ξ : κ → ℤ) (B V : ℕ → ℤ) :
    (j : ℕ) → SampleOrigins k j κ → ℤ → State k j → HistoryReconstruction.Tree j → Prop
  | 0,_,s,x,_ => CurrentRootArithmetic k 0 s x
  | j+1,o,s,x,t => CurrentRootArithmetic k (j+1) s x ∧
      NodeArithmetic k j x s t.1.1 t.1.2 (V j) ∧
      IntegerNodeSupport k j s t.1.1 t.1.2 x ∧
      (∀ i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i},
        IsCoprime (reconstructedPivot k j x s t.1.1 t.1.2) (ξ (o.outside i))) ∧
      sampledHistoryArithmetic k ξ B V j (o.child true) t.1.1
        (childState k j true x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ∧
      sampledHistoryArithmetic k ξ B V j (o.child false) t.1.2
        (childState k j false x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

theorem sampledTransfer_iff (k : ℕ) (ξ : κ → ℤ) (B V : ℕ → ℤ)
    (g : (j : ℕ) → ℤ → List (Guard (schedule k j).Slot))
    (j : ℕ) (o : SampleOrigins k j κ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    SampledTransferSupport k ξ (fun j _ => B j) (fun j _ => V j)
      (fun j s x _ => canonicalMask k g j s x) j o s (evalExpressions a e) t ↔
      sampledHistoryArithmetic k ξ B V j o s (evalExpressions a e) t ∧
        guardsHold (historyGuards k B V g j s e t) a := by
  induction j generalizing s with
  | zero =>
    simp only [SampledTransferSupport,sampledHistoryArithmetic,historyGuards,
      guardsHold_append,guardsHold_substitute,canonicalMask]
    rw [currentRootSupport_iff]
    tauto
  | succ j ih =>
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hl := ih (o.child true) t.1.1 (childExpressions k j true e P) t.2.1
    have hr := ih (o.child false) t.1.2 (childExpressions k j false e P) t.2.2
    simp only [childExpressions_eval,pivotExpression_eval,P,canonicalMask] at hl hr
    simp only [SampledTransferSupport,sampledHistoryArithmetic,historyGuards,
      guardsHold_append,guardsHold_substitute,canonicalMask]
    rw [currentRootSupport_iff,nodeSupported_iff,hl,hr]
    tauto

theorem prime_canonicalTransfer_iff {k Q : ℕ} (B V : ℕ → ℤ)
    (g : (j : ℕ) → ℤ → List (Guard (schedule k j).Slot))
    (j : ℕ) (hj : j ≤ k) (s : ℤ) (width : Role → ℕ)
    (p : (schedule k j).Constituent width → Preliminaries.PrimeUpTo Q)
    (hinj : Function.Injective (fun i => (p i).val))
    (e : Expressions (ι:=ι) k j) (a : ι → ℤ)
    (he : evalExpressions a e = constituentSampleState (schedule k j) width p)
    (t : HistoryReconstruction.Tree j) :
    TransferSupport k (fun j _ => B j) (fun j _ => V j)
      (fun j s x _ => canonicalMask k g j s x) j s (evalExpressions a e) t ↔
      sampledHistoryArithmetic k (constituentSampleState (schedule k j) width p) B V j
        (SampleOrigins.root k j) s (evalExpressions a e) t ∧
        guardsHold (historyGuards k B V g j s e t) a := by
  rw [← sampledTransfer_iff]
  rw [he]
  exact prime_transferSupport_iff_sampled _ _ _ j hj s width p hinj t

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
