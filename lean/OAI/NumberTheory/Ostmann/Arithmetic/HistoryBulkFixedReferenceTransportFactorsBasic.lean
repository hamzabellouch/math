import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportAssigned
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeSupportedIntegral
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorCRT
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedXiTransportBasic

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkFixedReferenceTransport
open Construction HistoryPairBulkTransport HistorySignedDecode HistorySignedResidues
open HistorySignedSpectatorCRT HistorySignedXiTransport

theorem assigned_compensationProduct_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (s t : ℤ) (gp gm gp' gm' : ℕ)
    (x₀ x : SourceAssignment sources (Template.current seed l))
    (c : HistoryChoices sources seed V l) :
    (assignedHistory sources seed V l s gp gm x₀ c).compensationProduct=
      (assignedHistory sources seed V l t gp' gm' x c).compensationProduct :=
  decoded_compensationProduct_eq sources seed V l _ _ c

theorem decoded_frequencies_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (hf : a.frequency=b.frequency) :
    (decodeHistory sources seed V l a c).frequencies=
      (decodeHistory sources seed V l b c).frequencies := by
  induction l generalizing a b with
  | zero => simpa only [decodeHistory,History.frequencies] using congrArg (fun s=>[s]) hf
  | succ l ih =>
    simp only [decodeHistory,History.frequencies]
    apply congrArg₂ List.cons hf
    exact congrArg₂ List.append (ih _ _ c.2.2.2.1 rfl) (ih _ _ c.2.2.2.2 rfl)

theorem decoded_rebuild_positiveIntegral (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a : State)
    (c : HistoryChoices sources seed V l)
    (hs : (decodeHistory sources seed V l a c).Supported V outside) :
    (rebuild (decodeHistory sources seed V l a c) a.giantPlus a.giantMinus).PositiveIntegral := by
  simpa only [rebuild_decodeHistory,SignedState.ofState] using
    signedDecode_ofState_positiveIntegral_of_supported sources seed V l a c outside hs

theorem decoded_rebuild_toHistory (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a : State)
    (c : HistoryChoices sources seed V l)
    (hs : (decodeHistory sources seed V l a c).Supported V outside) :
    (rebuild (decodeHistory sources seed V l a c) a.giantPlus a.giantMinus).toHistory=
      decodeHistory sources seed V l a c := by
  simpa only [rebuild_decodeHistory,SignedState.ofState] using
    signedDecode_ofState_toHistory_of_supported sources seed V l a c outside hs

theorem decoded_leafProduct_eq_residue (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a : State)
    (c : HistoryChoices sources seed V l)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (hf : ∀s∈(decodeHistory sources seed V l a c).frequencies,Nat.Coprime s.natAbs outside.prod)
    (g : (q:ℕ)→ZMod q→ℂ) :
    (decodeHistory sources seed V l a c).leafProduct (Construction.spectatorFactor g outside)=
      residueSpectator g outside outside.prod (decodeHistory sources seed V l a c)
        a.giantPlus a.giantMinus := by
  let h := decodeHistory sources seed V l a c
  have hi := decoded_rebuild_positiveIntegral sources seed V outside l a c hs
  have he := residueSpectator_intCast h g outside (divisorProduct h) outside.prod
    (fun q hq=>List.dvd_prod hq) (divisorData_actual h hs)
    (divisorProduct_coprime_outside h hs hf) a.giantPlus a.giantMinus hi.integralGuard
  rw [HistorySignedSpectator.spectatorProduct_eq_projection g outside _ hi.nonnegative,
    decoded_rebuild_toHistory sources seed V outside l a c hs] at he
  simpa only [Int.cast_natCast] using he.symm

theorem assigned_pair_leafProduct_eq_residue (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (s t : ℤ) (gp gm : ℕ)
    (x y : SourceAssignment sources (Template.current seed l))
    (c e : HistoryChoices sources seed V l)
    (hs : (assignedHistory sources seed V l s gp gm x c).Supported V outside)
    (ks : (assignedHistory sources seed V l t gp gm y e).Supported V outside)
    (hf : ∀u∈(assignedHistory sources seed V l s gp gm x c).frequencies++
      (assignedHistory sources seed V l t gp gm y e).frequencies,Nat.Coprime u.natAbs outside.prod)
    (g : (q:ℕ)→ZMod q→ℂ) :
    (assignedHistory sources seed V l s gp gm x c).leafProduct (Construction.spectatorFactor g outside)*
      conj ((assignedHistory sources seed V l t gp gm y e).leafProduct (Construction.spectatorFactor g outside))=
    residuePairSpectator g outside outside.prod
      (assignedHistory sources seed V l s gp gm x c)
      (assignedHistory sources seed V l t gp gm y e) (gp,gm) := by
  rw [residuePairSpectator]
  exact congrArg₂ (fun a b : ℂ=>a*conj b)
    (decoded_leafProduct_eq_residue sources seed V outside l _ c hs
      (fun u hu=>hf u (List.mem_append_left _ hu)) g)
    (decoded_leafProduct_eq_residue sources seed V outside l _ e ks
      (fun u hu=>hf u (List.mem_append_right _ hu)) g)

end Ostmann.Arithmetic.HistoryBulkFixedReferenceTransport

end

end OAI
