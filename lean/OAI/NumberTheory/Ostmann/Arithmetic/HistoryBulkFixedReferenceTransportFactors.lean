import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTransportFactorsBasic

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkFixedReferenceTransport
open Construction HistoryPairBulkTransport HistorySignedDecode HistorySignedResidues
open HistorySignedSpectatorCRT HistoryRepresentativeSourceSeparation

theorem assigned_frequencies_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (s : ℤ) (gp gm gp' gm' : ℕ)
    (x₀ x : SourceAssignment sources (Template.current seed l))
    (c : HistoryChoices sources seed V l) :
    (assignedHistory sources seed V l s gp gm x₀ c).frequencies=
      (assignedHistory sources seed V l s gp' gm' x c).frequencies :=
  decoded_frequencies_eq sources seed V l _ _ c rfl

theorem assigned_pair_leafProduct_eq_residue_of_reference
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (outside : List ℕ) (l : ℕ) (s t : ℤ) (gp gm gp' gm' : ℕ)
    (x₀ y₀ x y : SourceAssignment sources (Template.current seed l))
    (c e : HistoryChoices sources seed V l)
    (had : PairAdmissible (assignedHistory sources seed V l s gp gm x₀ c)
      (assignedHistory sources seed V l t gp gm y₀ e) outside)
    (hs : (assignedHistory sources seed V l s gp' gm' x c).Supported V outside)
    (ks : (assignedHistory sources seed V l t gp' gm' y e).Supported V outside)
    (g : (q:ℕ)→ZMod q→ℂ) :
    (assignedHistory sources seed V l s gp' gm' x c).leafProduct (Construction.spectatorFactor g outside)*
      conj ((assignedHistory sources seed V l t gp' gm' y e).leafProduct (Construction.spectatorFactor g outside))=
    residuePairSpectator g outside outside.prod
      (assignedHistory sources seed V l s gp' gm' x c)
      (assignedHistory sources seed V l t gp' gm' y e) (gp',gm') := by
  apply assigned_pair_leafProduct_eq_residue sources seed V outside l s t gp' gm' x y c e hs ks _ g
  intro u hu
  rw [←assigned_frequencies_eq sources seed V l s gp gm gp' gm' x₀ x c,
    ←assigned_frequencies_eq sources seed V l t gp gm gp' gm' y₀ y e] at hu
  have hc : Nat.Coprime
      (FrequencyPrecision.product ((assignedHistory sources seed V l s gp gm x₀ c).frequencies++
        (assignedHistory sources seed V l t gp gm y₀ e).frequencies)) outside.prod := by
    simpa only [pow_one] using (had.2.2.2 1).2.2.2.1.symm
  exact hc.of_dvd_left (FrequencyPrecision.frequency_dvd_product hu)

end Ostmann.Arithmetic.HistoryBulkFixedReferenceTransport

end

end OAI
