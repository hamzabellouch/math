import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealizationUnitsSources
import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction

theorem sourceMass_coprime_paired_frequency {sources : SourceFamily}
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ} (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hfreq : ∀j ≤ l,∀origin,(sources origin).AboveFrequency (V j))
    (q : SmallSlot) (hq : sourceMass sources q≠0) (n : ℕ) :
    Nat.Coprime q.value (FrequencyPrecision.product (h.frequencies++k.frequencies)^n) :=
  small_coprime_frequency_power h k hs ks q.value (sourceMass_value_prime hq)
    (fun j hj=>sourceMass_value_gt (hfreq j hj) hq) n

theorem decoded_frequencyUnits (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hroot : ∀q∈a.small,sourceMass sources q≠0)
    (hc : choicesMass sources seed V l c≠0)
    (hfreq : ∀j ≤ l,∀origin,(sources origin).AboveFrequency (V j)) :
    FrequencyUnits (FrequencyPrecision.product (h.frequencies++k.frequencies))
      (decodeHistory sources seed V l a c) := by
  apply decoded_frequencyUnits_of_source sources seed V _ _ l a c ha hroot hc
  intro q hq
  simpa only [pow_one] using sourceMass_coprime_paired_frequency h k hs ks hfreq q hq 1

theorem decoded_outer_frequencyUnits (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (giant : PrimeSource) (outside : List ℕ) (l : ℕ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (x : OuterSample sources (Template.current seed l) giant) (s : ℤ)
    (c : HistoryChoices sources seed V l)
    (hx : (outerPrior sources (Template.current seed l) giant).mass x≠0)
    (hc : choicesMass sources seed V l c≠0)
    (hfreq : ∀j ≤ l,∀origin,(sources origin).AboveFrequency (V j)) :
    FrequencyUnits (FrequencyPrecision.product (h.frequencies++k.frequencies))
      (decodeHistory sources seed V l (outerState sources (Template.current seed l) giant x s) c) := by
  have hx' : giant.law.mass x.1*(giant.law.mass x.2.1*
      (assignmentPrior sources (Template.current seed l)).mass x.2.2)≠0 := hx
  have hmass := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hx').2).2
  apply decoded_frequencyUnits sources seed V outside l h k hs ks _ c
  · exact Template.assignedSlots_matches _ _ _
  · exact assignedSlots_source_mass_ne_zero _ _ _ hmass
  · exact hc
  · exact hfreq

theorem decoded_outer_pair_frequencyUnits (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (giant : PrimeSource) (outside : List ℕ) (l : ℕ)
    (x y : OuterSample sources (Template.current seed l) giant) (s t : ℤ)
    (c e : HistoryChoices sources seed V l)
    (hx : (outerPrior sources (Template.current seed l) giant).mass x≠0)
    (hy : (outerPrior sources (Template.current seed l) giant).mass y≠0)
    (hc : choicesMass sources seed V l c≠0) (he : choicesMass sources seed V l e≠0)
    (hfreq : ∀j ≤ l,∀origin,(sources origin).AboveFrequency (V j))
    (hs : (decodeHistory sources seed V l (outerState sources (Template.current seed l) giant x s) c).Supported V outside)
    (ks : (decodeHistory sources seed V l (outerState sources (Template.current seed l) giant y t) e).Supported V outside) :
    let h := decodeHistory sources seed V l (outerState sources (Template.current seed l) giant x s) c
    let k := decodeHistory sources seed V l (outerState sources (Template.current seed l) giant y t) e
    let R := FrequencyPrecision.product (h.frequencies++k.frequencies)
    FrequencyUnits R h ∧ FrequencyUnits R k := by
  dsimp only
  exact ⟨decoded_outer_frequencyUnits sources seed V giant outside l _ _ hs ks x s c hx hc hfreq,
    decoded_outer_frequencyUnits sources seed V giant outside l _ _ hs ks y t e hy he hfreq⟩

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
