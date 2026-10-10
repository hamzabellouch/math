import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationModuli
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportAssigned

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkReferenceNewModuli
open Construction HistoryCRTIntegration HistoryPairBulkTransport
variable {l : ℕ}

def newComparisonModulus (newh oldh oldk : History l) (outside : List ℕ) (K : ℕ) : ℕ :=
  rootModulus newh * outside.prod * frequencyModulus oldh oldk (K+2) *
    representativeModulus oldh oldk

def newComparisonModuli (newh oldh oldk : History l) (outside : List ℕ) (K : ℕ) : Fin 4 → ℕ :=
  fourModuli (rootModulus newh) outside.prod (frequencyModulus oldh oldk (K+2))
    (representativeModulus oldh oldk)

theorem newComparisonModuli_prod (newh oldh oldk : History l) (outside : List ℕ) (K : ℕ) :
    (∏i,newComparisonModuli newh oldh oldk outside K i) =
      newComparisonModulus newh oldh oldk outside K := fourModuli_prod _ _ _ _

theorem rootModulus_pos_of_primeSmall (h : History l) (hp : h.root.PrimeSmall) :
    0 < rootModulus h := by
  apply List.prod_pos
  intro n hn
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hn
  exact (hp q hq).pos

@[simp] theorem rootModulus_assignedHistory (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (s : ℤ) (gp gm : ℕ)
    (x : SourceAssignment sources (Template.current seed l))
    (c : HistoryChoices sources seed V l) :
    rootModulus (assignedHistory sources seed V l s gp gm x c) =
      ((assignedSlots sources (Template.current seed l) x).map SmallSlot.value).prod := by
  simp only [rootModulus,assignedHistory,decodeHistory_root,assignedRoot]

theorem assigned_rootModulus_pos (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (s : ℤ) (gp gm : ℕ)
    (x : SourceAssignment sources (Template.current seed l))
    (c : HistoryChoices sources seed V l) :
    0 < rootModulus (assignedHistory sources seed V l s gp gm x c) := by
  apply rootModulus_pos_of_primeSmall
  simpa only [assignedHistory,decodeHistory_root,assignedRoot,State.PrimeSmall] using
    assignedSlots_prime sources (Template.current seed l) x

theorem newComparisonModuli_pos {V : ℕ → ℕ} {outside : List ℕ}
    (newh oldh oldk : History l) (hp : newh.root.PrimeSmall)
    (hs : oldh.Supported V outside) (ks : oldk.Supported V outside)
    (hout : ∀p∈outside,p.Prime) (K : ℕ) (i : Fin 4) :
    0 < newComparisonModuli newh oldh oldk outside K i := by
  fin_cases i
  · exact rootModulus_pos_of_primeSmall newh hp
  · exact outsideModulus_pos hout
  · exact frequencyModulus_pos oldh oldk hs ks (K+2)
  · exact representativeModulus_pos oldh oldk hs ks

theorem newComparisonModuliNeZero {V : ℕ → ℕ} {outside : List ℕ}
    (newh oldh oldk : History l) (hp : newh.root.PrimeSmall)
    (hs : oldh.Supported V outside) (ks : oldk.Supported V outside)
    (hout : ∀p∈outside,p.Prime) (K : ℕ) :
    ∀i,NeZero (newComparisonModuli newh oldh oldk outside K i) :=
  fun i => ⟨ne_of_gt (newComparisonModuli_pos newh oldh oldk hp hs ks hout K i)⟩

theorem newComparisonModulus_pos {V : ℕ → ℕ} {outside : List ℕ}
    (newh oldh oldk : History l) (hp : newh.root.PrimeSmall)
    (hs : oldh.Supported V outside) (ks : oldk.Supported V outside)
    (hout : ∀p∈outside,p.Prime) (K : ℕ) :
    0 < newComparisonModulus newh oldh oldk outside K := by
  rw [←newComparisonModuli_prod]
  exact Finset.prod_pos (fun i _ => newComparisonModuli_pos newh oldh oldk hp hs ks hout K i)

end Ostmann.Arithmetic.HistoryBulkReferenceNewModuli

end

end OAI
