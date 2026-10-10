import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceNewModuliSources

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkReferenceNewModuli
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryCRTIntegration HistoryPairBulkTransport HistoryBulkSourceCollision
open HistoryOccurrenceVariables HistoryRepresentativeSourceSeparation HistoryPairRepresentatives
open HistorySymbolicEncoding HistoryFrequencyResidues
variable {l : ℕ}

def NewCRTCompatible (newh oldh oldk : History l) (outside : List ℕ) (K : ℕ) : Prop :=
  Nat.Coprime (rootModulus newh) outside.prod ∧
  Nat.Coprime (rootModulus newh) (frequencyModulus oldh oldk (K+2)) ∧
  Nat.Coprime (rootModulus newh) (representativeModulus oldh oldk) ∧
  Nat.Coprime outside.prod (frequencyModulus oldh oldk (K+2)) ∧
  Nat.Coprime outside.prod (representativeModulus oldh oldk) ∧
  Nat.Coprime (frequencyModulus oldh oldk (K+2)) (representativeModulus oldh oldk)

theorem newComparisonModuli_pairwise (newh oldh oldk : History l) (outside : List ℕ) (K : ℕ)
    (hc : NewCRTCompatible newh oldh oldk outside K) :
    Pairwise (fun i j => (newComparisonModuli newh oldh oldk outside K i).Coprime
      (newComparisonModuli newh oldh oldk outside K j)) := fourModuli_pairwise _ _ _ _ hc

variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth : ℕ} {E : Finset ℕ}

theorem assigned_newCRTCompatible (C : InitialSourceChoice d Bs BD Bz depth L E)
    (spectator : PrimeSource) (hsep : C.CrossRoleSeparation spectator)
    (V : ℕ → ℕ) (outside : List ℕ) (l K : ℕ) (s t snew : ℤ)
    (gp gm gpnew gmnew : ℕ)
    (x₀ y₀ x : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l))
    (c e cnew : HistoryChoices C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l)
    (hs : (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c).Supported V outside) (ks : (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l t gp gm y₀ e).Supported V outside)
    (hp : PairAdmissible (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l t gp gm y₀ e) outside)
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l)).mass x≠0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l c≠0)
    (he : choicesMass C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l e≠0)
    (hfixed : ∀i:Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length,((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (hout : ∀q∈outside,∃p:spectator.Sample,p.val=q ∧ spectator.law.mass p≠0)
    (hfreq : ∀j ≤ l,∀origin,(C.sources origin).AboveFrequency (V j)) :
    NewCRTCompatible (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l snew gpnew gmnew x cnew) (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l t gp gm y₀ e) outside K := by
  have hT : ∀q∈(Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l),q∈(Template.initial (2*(bulkSize depth L/2)) depth) := fun q hq => Template.mem_current_mem_seed hq
  have hcrt := hp.2.2.2 (K+2)
  change Nat.Coprime (rootModulus (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c)) outside.prod ∧
    Nat.Coprime (rootModulus (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c)) (frequencyModulus (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l t gp gm y₀ e) (K+2)) ∧
    Nat.Coprime (rootModulus (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c)) (representativeModulus (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l t gp gm y₀ e)) ∧
    Nat.Coprime outside.prod (frequencyModulus (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l t gp gm y₀ e) (K+2)) ∧
    Nat.Coprime outside.prod (representativeModulus (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l t gp gm y₀ e)) ∧
    Nat.Coprime (frequencyModulus (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l t gp gm y₀ e) (K+2)) (representativeModulus (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l t gp gm y₀ e)) at hcrt
  refine ⟨?_,?_,?_,hcrt.2.2.2.1,hcrt.2.2.2.2.1,hcrt.2.2.2.2.2⟩
  · rw [rootModulus_assignedHistory]
    apply assigned_product_coprime_outside C spectator hsep (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l) hT x₀ x hx hfixed hout
    simpa only [rootModulus_assignedHistory] using hcrt.1
  · rw [rootModulus_assignedHistory]
    exact source_slots_product_coprime C.sources _
      (fun q hq => sourceMass_coprime_paired_frequency (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l t gp gm y₀ e) hs ks hfreq q hq (K+2))
      _ (assignedSlots_source_mass_ne_zero C.sources (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l) x hx)
  · rw [rootModulus_assignedHistory]
    apply assigned_product_coprime_representatives C spectator hsep (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l) hT x₀ x hx hfixed
      (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l t gp gm y₀ e) (assignedLabels C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l s gp gm x₀ c) (assignedLabels C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l t gp gm y₀ e) hs ks
      (decoded_internalSlot_mass C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l (assignedRoot C.sources (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l) s gp gm x₀) c hc)
      (decoded_internalSlot_mass C.sources (Template.initial (2*(bulkSize depth L/2)) depth) V l (assignedRoot C.sources (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l) t gp gm y₀) e he)
    simpa only [rootModulus_assignedHistory] using hcrt.2.2.1

end Ostmann.Arithmetic.HistoryBulkReferenceNewModuli

end

end OAI
