import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceReindexPositive
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWeight

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

def canonicalHistoryMask (k : ℕ) (leafMask : ℤ → State k 0 → Prop) :
    (j:ℕ) → ℤ → State k j → Prop
  | 0,s,x => leafMask s x
  | _+1,_,_ => True

def canonicalHistoryExtra (k : ℕ) (R : ℕ → Finset ℕ+) :
    (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop
  | 0,_,_,_ => True
  | j+1,s,x,t => ∃P∈R j,reconstructedPivot k j x s t.1.1 t.1.2=(P:ℤ)

@[simp] theorem canonicalHistoryMask_succ (k j : ℕ) (leafMask : ℤ → State k 0 → Prop)
    (s : ℤ) (x : State k (j+1)) : canonicalHistoryMask k leafMask (j+1) s x := trivial

theorem canonicalHistoryExtra_succ_iff (k j : ℕ) (R : ℕ → Finset ℕ+)
    (s : ℤ) (x : State k (j+1)) (t : HistoryReconstruction.Tree (j+1)) :
    canonicalHistoryExtra k R (j+1) s x t ↔
      ∃hp:0<reconstructedPivot k j x s t.1.1 t.1.2,
        positivePivotOfPos (reconstructedPivot k j x s t.1.1 t.1.2) hp∈R j := by
  constructor
  · rintro ⟨P,hP,he⟩
    have hp : 0<reconstructedPivot k j x s t.1.1 t.1.2 := by
      rw [he]
      exact_mod_cast P.pos
    refine ⟨hp,?_⟩
    have hval : positivePivotOfPos (reconstructedPivot k j x s t.1.1 t.1.2) hp=P := by
      apply Subtype.ext
      simp only [positivePivotOfPos,he,Int.toNat_natCast]
      rfl
    exact hval.symm ▸ hP
  · rintro ⟨hp,hP⟩
    refine ⟨positivePivotOfPos _ hp,hP,?_⟩
    simp only [positivePivotOfPos]
    exact (Int.toNat_of_nonneg hp.le).symm

theorem canonical_retainedHistoryWeight_succ (k j : ℕ)
    (B V : (j:ℕ) → State k (j+1) → ℤ) (R : ℕ → Finset ℕ+)
    (leafMask : ℤ → State k 0 → Prop) (X Δ W : ℝ)
    (s : ℤ) (x : State k (j+1)) (t : HistoryReconstruction.Tree (j+1))
    (hc : CurrentAtomSupport k (j+1) s x)
    (hn : NodeSupported k j x s t.1.1 t.1.2 (B j x) (V j x))
    (hi : IntegerNodeSupport k j s t.1.1 t.1.2 x) :
    retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
      X Δ W (j+1) s x t =
      if canonicalHistoryExtra k R (j+1) s x t then
        let P := reconstructedPivot k j x s t.1.1 t.1.2
        retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
          X Δ W j t.1.1 (childState k j true x P) t.2.1 *
        conj (retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
          X Δ W j t.1.2 (childState k j false x P) t.2.2)
      else 0 := by
  rw [retainedHistoryWeight_succ]
  simp only [localTransferSupport,hc,hn,hi,canonicalHistoryMask_succ,true_and,and_true]

end Ostmann.Characters.Template

end

end OAI
