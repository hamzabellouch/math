import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSupportReductionGuards

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedSupportReduction
open Construction HistorySignedDecode

def Reduced (V : ℕ→ℕ) (outside : List ℕ) : {l : ℕ}→SignedHistory l→Prop
  | _,h => RootData V h ∧ match h with
    | .leaf _ => True
    | @SignedHistory.node l a p u hp hm left right =>
      NodeRelations (l+1) a p u hp hm left.root right.root ∧
      LocalTests outside a p u hp hm left.root.frequency right.root.frequency ∧
      Reduced V outside left ∧ Reduced V outside right
termination_by l _=>l

lemma root_nonnegative {l : ℕ} {h : SignedHistory l} (hh : h.Nonnegative) :
    h.root.Nonnegative := by
  cases h with
  | leaf a => exact hh
  | node a p u hp hm left right => exact hh.1

theorem reduced_iff_projection {l : ℕ} (V : ℕ→ℕ) (outside : List ℕ)
    (h : SignedHistory l) (hn : h.Nonnegative) :
    Reduced V outside h↔HistorySupportReduction.Reduced V outside h.toHistory := by
  induction h with
  | leaf a =>
    simpa only [Reduced,HistorySupportReduction.Reduced,SignedHistory.toHistory,and_true]
      using rootData_iff_projection V (SignedHistory.leaf a)
  | @node l a p u hp hm left right il ir =>
    have hl := hn.2.2.1
    have hr := hn.2.2.2
    rw [Reduced,SignedHistory.toHistory,HistorySupportReduction.Reduced]
    simp only [toHistory_root]
    rw [rootData_iff_projection V (SignedHistory.node a p u hp hm left right),
      nodeRelations_iff_projection (l+1) a p u hp hm left.root right.root
        hn.1 (root_nonnegative hl) (root_nonnegative hr) hn.2.1,
      localTests_iff_projection outside a p u hp hm left.root.frequency right.root.frequency hn.1,
      il hl,ir hr]
    rfl

def Guarded (V : ℕ→ℕ) (outside : List ℕ) {l : ℕ} (h : SignedHistory l) : Prop :=
  h.PositiveIntegral ∧ h.root.toState.Coprime outside ∧ Reduced V outside h

theorem supported_of_guarded (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : SignedState) (c : HistoryChoices sources seed V l)
    (outside : List ℕ)
    (hlarge : HistorySupportReduction.LargePrimes V (decodeHistory sources seed V l a.toState c))
    (hg : Guarded V outside (signedDecode sources seed V l a c)) :
    (decodeHistory sources seed V l a.toState c).Supported V outside := by
  have he := signedDecode_toHistory_of_positiveIntegral sources seed V l a c hg.1
  apply (HistorySupportReduction.supported_iff_root_coprime_reduced _ hlarge).mpr
  constructor
  · simpa only [signedDecode_root,decodeHistory_root] using hg.2.1
  · rw [←he]
    exact (reduced_iff_projection V outside _ hg.1.nonnegative).mp hg.2.2

theorem supported_iff_guarded (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : SignedState) (c : HistoryChoices sources seed V l)
    (outside : List ℕ)
    (hlarge : HistorySupportReduction.LargePrimes V (decodeHistory sources seed V l a.toState c)) :
    (decodeHistory sources seed V l a.toState c).Supported V outside↔
      Guarded V outside (signedDecode sources seed V l a c) := by
  constructor
  · intro hs
    have hi := signedDecode_positiveIntegral_of_supported sources seed V l a c outside hs
    have he := signedDecode_toHistory_of_positiveIntegral sources seed V l a c hi
    have hr := (HistorySupportReduction.supported_iff_root_coprime_reduced _ hlarge).mp hs
    refine ⟨hi,?_,?_⟩
    · simpa only [signedDecode_root,decodeHistory_root] using hr.1
    · apply (reduced_iff_projection V outside _ hi.nonnegative).mpr
      simpa only [he] using hr.2
  · exact supported_of_guarded sources seed V l a c outside hlarge

theorem ofState_supported_iff_guarded (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (outside : List ℕ)
    (hlarge : HistorySupportReduction.LargePrimes V (decodeHistory sources seed V l a c)) :
    (decodeHistory sources seed V l a c).Supported V outside↔
      Guarded V outside (signedDecode sources seed V l (SignedState.ofState a) c) := by
  exact supported_iff_guarded sources seed V l (SignedState.ofState a) c outside hlarge

end Ostmann.Arithmetic.HistorySignedSupportReduction

end

end OAI
