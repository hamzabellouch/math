import OAI.NumberTheory.Ostmann.Characters.TemplateCompositePivotSupportFamilyCore

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open SymbolicHistory TemplateSupportRemoval
attribute [local instance] Classical.propDecidable
variable {κ : Type*}

def outsidePrimeRemainder (k : ℕ) (width : κ → ℕ)
    (a : (Σ r : κ, Fin (width r)) → ℤ)
    (B V : (j : ℕ) → State k (j+1) → ℤ)
    (extra : (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (j : ℕ) (o : SampleOrigins k j κ) (s : ℤ) (x : State k j)
    (t : HistoryReconstruction.Tree j) (i : Σ r : κ, Fin (width r)) : Prop :=
  TransferCoreSupport k B V extra j s x t ∧
    ∀ q : Σ r : κ, Fin (width r), q ≠ i → SelectedOutsideCoprime k q.1 (a q) j o s x t

theorem sampledTransferSupport_iff_remainder_family (k : ℕ) (width : κ → ℕ)
    (a : (Σ r : κ, Fin (width r)) → ℤ)
    (B V : (j : ℕ) → State k (j+1) → ℤ)
    (extra : (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (j : ℕ) (o : SampleOrigins k j κ) (s : ℤ)
    (e : Expressions (ι:=(Σ r : κ, Fin (width r))) k j)
    (t : HistoryReconstruction.Tree j) (i : Σ r : κ, Fin (width r)) :
    SampledTransferSupport k (fun r => ∏ b, a ⟨r,b⟩) B V extra j o s (evalExpressions a e) t ↔
      outsidePrimeRemainder k width a B V extra j o s (evalExpressions a e) t i ∧
        ∀ q ∈ outsidePivotFamily k i.1 j o s e t, IsCoprime (a i) (q.integerEval a) := by
  rw [sampledTransferSupport_iff_core_selected,← selectedOutsideCoprime_iff_family]
  constructor
  · intro h
    exact ⟨⟨h.1,fun q hq => h.2 q⟩,h.2 i⟩
  · rintro ⟨h,hi⟩
    refine ⟨h.1,?_⟩
    intro q
    by_cases hq : q=i
    · subst q; exact hi
    · exact h.2 q hq

theorem sampledTransfer_value_eq_family (k : ℕ) (width : κ → ℕ)
    (a : (Σ r : κ, Fin (width r)) → ℤ)
    (B V : (j : ℕ) → State k (j+1) → ℤ)
    (extra : (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (j : ℕ) (o : SampleOrigins k j κ) (s : ℤ)
    (e : Expressions (ι:=(Σ r : κ, Fin (width r))) k j)
    (t : HistoryReconstruction.Tree j) (i : Σ r : κ, Fin (width r))
    (p : ℕ) (hai : a i = (p:ℤ)) (mask : Bool) (z : ℂ) :
    (if mask then
      if SampledTransferSupport k (fun r => ∏ b, a ⟨r,b⟩) B V extra j o s
        (evalExpressions a e) t then z else 0 else 0) =
      familyCoprimeSupportedValue (outsidePivotFamily k i.1 j o s e t)
        (mask && decide (outsidePrimeRemainder k width a B V extra j o s
          (evalExpressions a e) t i)) p (fun q => q.integerEval a) z := by
  have hh := sampledTransferSupport_iff_remainder_family k width a B V extra j o s e t i
  rw [hai] at hh
  rw [hh]
  unfold familyCoprimeSupportedValue
  cases mask <;> by_cases hr : outsidePrimeRemainder k width a B V extra j o s
    (evalExpressions a e) t i <;> simp [hr]

theorem outsidePrimeRemainder.supported {k j : ℕ} {width : κ → ℕ}
    {a : (Σ r : κ, Fin (width r)) → ℤ} {B V extra o s x t i}
    (h : outsidePrimeRemainder k width a B V extra j o s x t i) :
    Supported k B V j s x t := h.1.supported j

end Ostmann.Characters.Template

end

end OAI
