import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceCollisionAncestors
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseIndependentPairRaw
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportAssigned

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistorySignedDecode HistorySignedNumerators HistoryOccurrenceVariables
open HistorySignedResidueFactorization HistorySymbolicEncoding HistoryBulkSupportConversePlan
open HistoryBulkDiagramParameters HistoryFrequencyResidues HistoryPairedFrequencyAverage
open HistorySignedSpectatorCRT HistoryPairBulkTransport

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
local notation "seed" => Template.initial (2*(bulkSize k L/2)) k

theorem independent_pair_supported_of_actual_source_tests
    (C : InitialSourceChoice d Bs BD Bz k L E) {spectator : PrimeSource}
    (hsep : C.CrossRoleSeparation spectator)
    (bSize sw : ℕ) (X tb td G : ℝ) (V : ℕ→ℕ) (outside : List ℕ) (l K : ℕ) (hle : l≤K)
    (x x' y y' : SourceAssignment C.sources (Template.current seed l)) (s t : ℤ)
    (Gp Gm Gp0 Gm0 : ℕ) (c e : HistoryChoices C.sources seed V l)
    (hs : (assignedHistory C.sources seed V l s Gp0 Gm0 y c).Supported V outside)
    (hs' : (assignedHistory C.sources seed V l t Gp0 Gm0 y' e).Supported V outside)
    (hnonbulk : ∀i : Fin (Template.current seed l).length,
      (Template.current seed l)[i].role≠.bulk → (x i:ℕ)=(y i:ℕ))
    (hnonbulk' : ∀i : Fin (Template.current seed l).length,
      (Template.current seed l)[i].role≠.bulk → (x' i:ℕ)=(y' i:ℕ))
    (hx' : (assignmentPrior C.sources (Template.current seed l)).mass x'≠0)
    (hx : (assignmentPrior C.sources (Template.current seed l)).mass x≠0)
    (hc : choicesMass C.sources seed V l c≠0) (he : choicesMass C.sources seed V l e≠0)
    (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (V j))
    (hp : 0<Gp) (hm : 0<Gm)
    (hroot : (assignedRoot C.sources (Template.current seed l) s Gp Gm x).Coprime outside)
    (hroot' : (assignedRoot C.sources (Template.current seed l) t Gp Gm x').Coprime outside)
    (ht : ReferenceTests bSize sw X tb td G C.sources seed V outside l
      (assignedRoot C.sources (Template.current seed l) s Gp0 Gm0 y)
      (assignedRoot C.sources (Template.current seed l) s Gp Gm x) c
      (assignedRoot_matches C.sources _ s Gp0 Gm0 y) (assignedRoot_matches C.sources _ s Gp Gm x) hs)
    (ht' : ReferenceTests bSize sw X tb td G C.sources seed V outside l
      (assignedRoot C.sources (Template.current seed l) t Gp0 Gm0 y')
      (assignedRoot C.sources (Template.current seed l) t Gp Gm x') e
      (assignedRoot_matches C.sources _ t Gp0 Gm0 y') (assignedRoot_matches C.sources _ t Gp Gm x') hs')
    (hR : independentReferenceIndicator K
      (assignedHistory C.sources seed V l s Gp0 Gm0 y c)
      (assignedHistory C.sources seed V l t Gp0 Gm0 y' e)
      (assignedHistory C.sources seed V l s Gp Gm x c)
      (assignedHistory C.sources seed V l t Gp Gm x' e) (Gp,Gm)≠0)
    (g : (q:ℕ)→ZMod q→ℂ) (hprime : ∀q∈outside,q.Prime)
    (hg : ∀q∈outside,g q 0=0) (houtfreq : ∀q∈outside,∀j≤l,V j<q)
    (hD : residuePairSpectator g outside outside.prod
      (assignedHistory C.sources seed V l s Gp Gm x c)
      (assignedHistory C.sources seed V l t Gp Gm x' e) (Gp,Gm)≠0) :
    (assignedHistory C.sources seed V l s Gp Gm x c).Supported V outside ∧
      (assignedHistory C.sources seed V l t Gp Gm x' e).Supported V outside := by
  apply pair_supported_of_independent_reference_and_raw_tests bSize sw X tb td G C.sources _ k V outside l K hle
    (assignedRoot C.sources _ s Gp0 Gm0 y) (assignedRoot C.sources _ t Gp0 Gm0 y')
    (assignedRoot C.sources _ s Gp Gm x) (assignedRoot C.sources _ t Gp Gm x') c e
    (assignedRoot_matches C.sources _ s Gp0 Gm0 y) (assignedRoot_matches C.sources _ t Gp0 Gm0 y')
    (assignedRoot_matches C.sources _ s Gp Gm x) (assignedRoot_matches C.sources _ t Gp Gm x')
    rfl rfl hs hs' rfl rfl
    (assignedSlots_erase_eq C.sources _ x y hnonbulk)
    (assignedSlots_erase_eq C.sources _ x' y' hnonbulk')
    (assignedSlots_source_mass_ne_zero C.sources _ x hx)
    (assignedSlots_source_mass_ne_zero C.sources _ x' hx') hc he hfreq hp hm hroot hroot'
    ?_ ?_ ht.lines ht'.lines ht.squares ht'.squares hR g hprime hg houtfreq hD ht.scalar ht'.scalar
  · exact HistoryBulkSourceCollision.newIntegerSample_ancestor_units C hsep V l x hx c hc s Gp Gm Gp Gm
  · exact HistoryBulkSourceCollision.newIntegerSample_ancestor_units C hsep V l x' hx' e he t Gp Gm Gp Gm

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
