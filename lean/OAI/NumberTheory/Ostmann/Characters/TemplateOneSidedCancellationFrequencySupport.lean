import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationFrequencyGuards

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template
attribute [local instance] Classical.propDecidable
variable {ι κ : Type*}

def historyFrequencyBounds (V : ℕ → ℤ) :
    (j : ℕ) → ℤ → HistoryReconstruction.Tree j → Prop
  | 0,s,_ => s ≠ 0
  | j+1,s,t => s ≠ 0 ∧ |t.1.1| ≤ V j ∧ |t.1.2| ≤ V j ∧
      historyFrequencyBounds V j t.1.1 t.2.1 ∧ historyFrequencyBounds V j t.1.2 t.2.2

theorem historyFrequencyBounds_root (V : ℕ → ℤ) (j : ℕ) (s : ℤ)
    (t : HistoryReconstruction.Tree j) (h : historyFrequencyBounds V j s t) : s ≠ 0 := by
  cases j with
  | zero => exact h
  | succ j => exact h.1

def frequencyArithmetic (k : ℕ) (V : ℕ → ℤ) :
    (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop
  | 0,s,x,_ => CurrentRootArithmetic k 0 s x
  | j+1,s,x,t => CurrentRootArithmetic k (j+1) s x ∧
      NodeArithmetic k j x s t.1.1 t.1.2 (V j) ∧
      IntegerNodeSupport k j s t.1.1 t.1.2 x ∧
      frequencyArithmetic k V j t.1.1
        (childState k j true x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ∧
      frequencyArithmetic k V j t.1.2
        (childState k j false x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

def outsideHistorySupport (k : ℕ) (ξ : κ → ℤ) :
    (j : ℕ) → SampleOrigins k j κ → ℤ → State k j → HistoryReconstruction.Tree j → Prop
  | 0,_,_,_,_ => True
  | j+1,o,s,x,t =>
      (∀ i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i},
        IsCoprime (reconstructedPivot k j x s t.1.1 t.1.2) (ξ (o.outside i))) ∧
      outsideHistorySupport k ξ j (o.child true) t.1.1
        (childState k j true x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ∧
      outsideHistorySupport k ξ j (o.child false) t.1.2
        (childState k j false x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

theorem sampledHistoryArithmetic_split (k : ℕ) (ξ : κ → ℤ) (B V : ℕ → ℤ)
    (j : ℕ) (o : SampleOrigins k j κ) (s : ℤ) (x : State k j)
    (t : HistoryReconstruction.Tree j) :
    sampledHistoryArithmetic k ξ B V j o s x t ↔
      frequencyArithmetic k V j s x t ∧ outsideHistorySupport k ξ j o s x t := by
  induction j generalizing s with
  | zero => simp only [sampledHistoryArithmetic,frequencyArithmetic,outsideHistorySupport,and_true]
  | succ j ih =>
    simp only [sampledHistoryArithmetic,frequencyArithmetic,outsideHistorySupport,ih]
    tauto

def historyResidueGuards (k : ℕ) :
    (j : ℕ) → ℤ → Expressions (ι:=ι) k j → HistoryReconstruction.Tree j → List (ResidueGuard ι)
  | 0,s,e,_ => rootResidueGuards k 0 s e
  | j+1,s,e,t =>
      let P := pivotExpression k j e s t.1.1 t.1.2
      rootResidueGuards k (j+1) s e ++ (nodeResidueGuards k j e s t.1.1 t.1.2 ++
      (historyResidueGuards k j t.1.1 (childExpressions k j true e P) t.2.1 ++
        historyResidueGuards k j t.1.2 (childExpressions k j false e P) t.2.2))

theorem pivotExpression_good_of_nodeArithmetic (k j : ℕ)
    (e : Expressions (ι:=ι) k (j+1)) (s v w V : ℤ) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i))
    (h : NodeArithmetic k j (evalExpressions a e) s v w V) :
    HistoryReconstruction.Good a (pivotExpression k j e s v w) := by
  have hL := copiedExpression_good k j true e a he
  have hR := copiedExpression_good k j false e a he
  exact ⟨⟨⟨⟨trivial,hR.1⟩,⟨trivial,hL.1⟩⟩,h.root_ne_zero⟩,
    (pivotExpression_integral_iff k j e s v w a he).mpr h.integral⟩

theorem rootResidueGuards_iff_arithmetic (k j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (a : ι → ℤ) (hs : s ≠ 0)
    (he : ∀ i, HistoryReconstruction.Good a (e i)) :
    (∀ q ∈ rootResidueGuards k j s e, q.holds a) ↔
      CurrentRootArithmetic k j s (evalExpressions a e) := by
  rw [rootResidueGuards_holds]
  exact ⟨fun h => ⟨hs,fun i => (h i).2⟩,fun h i => ⟨(he i).2,h.root_coprime i⟩⟩

theorem historyResidueGuards_holds (k : ℕ) (V : ℕ → ℤ) (j : ℕ)
    (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i))
    (hf : historyFrequencyBounds V j s t) :
    (∀ q ∈ historyResidueGuards k j s e t, q.holds a) ↔
      frequencyArithmetic k V j s (evalExpressions a e) t := by
  induction j generalizing s with
  | zero => exact rootResidueGuards_iff_arithmetic k 0 s e a hf he
  | succ j ih =>
    let P := pivotExpression k j e s t.1.1 t.1.2
    simp only [historyResidueGuards,List.mem_append,or_imp,forall_and]
    rw [rootResidueGuards_iff_arithmetic k (j+1) s e a hf.1 he,
      nodeResidueGuards_holds k j e s t.1.1 t.1.2 (V j) a he hf.1 hf.2.1 hf.2.2.1]
    constructor
    · rintro ⟨hc,⟨hn,hi⟩,hl,hr⟩
      have hp := pivotExpression_good_of_nodeArithmetic k j e _ _ _ _ a he hn
      have hgl := childExpressions_preserves k j true e P _ he hp
      have hgr := childExpressions_preserves k j false e P _ he hp
      have ihl := (ih t.1.1 (childExpressions k j true e P) t.2.1 hgl hf.2.2.2.1).mp hl
      have ihr := (ih t.1.2 (childExpressions k j false e P) t.2.2 hgr hf.2.2.2.2).mp hr
      simp only [childExpressions_eval,pivotExpression_eval,P] at ihl ihr
      exact ⟨hc,hn,hi,ihl,ihr⟩
    · rintro ⟨hc,hn,hi,hl,hr⟩
      have hp := pivotExpression_good_of_nodeArithmetic k j e _ _ _ _ a he hn
      have hgl := childExpressions_preserves k j true e P _ he hp
      have hgr := childExpressions_preserves k j false e P _ he hp
      have ihl := ih t.1.1 (childExpressions k j true e P) t.2.1 hgl hf.2.2.2.1
      have ihr := ih t.1.2 (childExpressions k j false e P) t.2.2 hgr hf.2.2.2.2
      simp only [childExpressions_eval,pivotExpression_eval,P] at ihl ihr
      exact ⟨hc,⟨hn,hi⟩,ihl.mpr hl,ihr.mpr hr⟩

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
