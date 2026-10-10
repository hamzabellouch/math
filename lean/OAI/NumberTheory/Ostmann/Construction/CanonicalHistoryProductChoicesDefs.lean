import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportSources

namespace OAI

noncomputable section
namespace Ostmann.Construction
open CanonicalOccurrenceTransport

def FrequencyChoices (V : ℕ → ℕ) : ℕ → Type
  | 0 => Unit
  | l+1 => AllowedFrequency V l × AllowedFrequency V l ×
      FrequencyChoices V l × FrequencyChoices V l

instance frequencyChoicesFintype (V : ℕ → ℕ) : (l : ℕ) → Fintype (FrequencyChoices V l)
  | 0 => inferInstanceAs (Fintype Unit)
  | l+1 => by
    letI := frequencyChoicesFintype V l
    exact inferInstanceAs (Fintype (AllowedFrequency V l × AllowedFrequency V l ×
      FrequencyChoices V l × FrequencyChoices V l))

abbrev InternalSourceDraws (sources : SourceFamily) (seed : List SourceSlot) (l : ℕ) :=
  ∀ i : Internal seed l, (sources (internalSource seed i).origin).Sample

instance internalSourceDrawsFintype (sources : SourceFamily) (seed : List SourceSlot) (l : ℕ) :
    Fintype (InternalSourceDraws sources seed l) := by
  classical
  exact inferInstanceAs (Fintype (∀ i : Internal seed l,
    (sources (internalSource seed i).origin).Sample))

def internalSourcePrior (sources : SourceFamily) (seed : List SourceSlot) (l : ℕ) :
    FinitePrior (InternalSourceDraws sources seed l) := by
  classical
  exact dependentProductPrior (fun i : Internal seed l => (sources (internalSource seed i).origin).law)

def historyFrequencies (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) :
    (l : ℕ) → HistoryChoices sources seed V l → FrequencyChoices V l
  | 0, _ => ()
  | l+1, c => ⟨c.1,c.2.1,
      historyFrequencies sources seed V l c.2.2.2.1,
      historyFrequencies sources seed V l c.2.2.2.2⟩

def historyDraws (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) :
    (l : ℕ) → HistoryChoices sources seed V l → InternalSourceDraws sources seed l
  | 0, _, i => Empty.elim i
  | _level+1, c, .inl i => c.2.2.1 i
  | l+1, c, .inr (.inl i) => historyDraws sources seed V l c.2.2.2.1 i
  | l+1, c, .inr (.inr i) => historyDraws sources seed V l c.2.2.2.2 i

def assembleHistoryChoices (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) :
    (l : ℕ) → FrequencyChoices V l → InternalSourceDraws sources seed l → HistoryChoices sources seed V l
  | 0, _, _ => ()
  | l+1, f, x => ⟨f.1,f.2.1,(fun i => x (.inl i)),
      assembleHistoryChoices sources seed V l f.2.2.1 (fun i => x (.inr (.inl i))),
      assembleHistoryChoices sources seed V l f.2.2.2 (fun i => x (.inr (.inr i)))⟩

end Ostmann.Construction

end

end OAI
