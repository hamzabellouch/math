import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationIntegral
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationRoot
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistorySignedDecode HistorySignedNumerators HistorySupportReduction
open HistorySignedSupportReduction HistorySignedSpectator
open HistoryPairPattern HistoryPairRows HistoryFrequencyResidues

def FactoredResidueGuard (K : ℕ) {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h h' : History l) (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (Xp Xm : ℤ) : Prop :=
  RootSmallUnits h Xp Xm ∧ RootSmallUnits h' Xp Xm ∧
    FrequencyGiantCoprime (rebuild h Xp Xm) ∧ FrequencyGiantCoprime (rebuild h' Xp Xm) ∧
    pairedSignedLeafAdmissible K h h' Xp Xm ∧ OwnPrimeLines h h' hs hs' Xp Xm ∧
    OwnPrimeSquareLines h h' hs hs' Xp Xm

theorem residueGuarded_pair_iff_factored_of_outsideUnits
    (K : ℕ) {l : ℕ} (h h' : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (hroot : RootGiantsAgree h h')
    (hlarge : LargePrimes V h) (hlarge' : LargePrimes V h')
    (hu : FrequencyUnits (pairedFrequencyProduct h h') h)
    (hu' : FrequencyUnits (pairedFrequencyProduct h h') h') (hle : l≤K)
    (hsame : frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h=
      frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h')
    (hx : ∀i : Occurrences h h', AncestorUnits h h'
      (fun j => (pairSample h h' j:ZMod (slot h h' i).value)) i)
    (hV : ∀i : Occurrences h h',∀j≤l,V j<(slot h h' i).value)
    (Xp Xm : ℤ) (ho : OutsideUnits outside (rebuild h Xp Xm))
    (ho' : OutsideUnits outside (rebuild h' Xp Xm)) :
    (ResidueGuarded V outside (rebuild h Xp Xm) ∧
      ResidueGuarded V outside (rebuild h' Xp Xm)) ↔
      FactoredResidueGuard K h h' hs hs' Xp Xm := by
  have hro : ∀q∈outside,Nat.Coprime Xp.natAbs q ∧ Nat.Coprime Xm.natAbs q := by
    simpa only [rebuild_root,GiantOutsideUnits] using ho.root
  have hra := residueRootCoprime_rebuild_iff h hs Xp Xm hro
  have hra' := residueRootCoprime_rebuild_iff h' hs' Xp Xm hro
  have hag := arithmeticGuards_rebuild_iff h hs hlarge Xp Xm
  have hag' := arithmeticGuards_rebuild_iff h' hs' hlarge' Xp Xm
  constructor
  · rintro ⟨hh,hh'⟩
    obtain ⟨hf,hsq,_⟩ := hag.mp hh.2.2
    obtain ⟨hf',hsq',_⟩ := hag'.mp hh'.2.2
    have hi := (integral_squares_iff_event_lines K h h' hs hs' hroot hlarge hlarge'
      hu hu' hle hsame hx hV Xp Xm (currentGiantUnits_of_frequencyGiantCoprime _ hf)
      (currentGiantUnits_of_frequencyGiantCoprime _ hf')).mp
      ⟨hh.2.1,hh'.2.1,(pairNumeratorSquares_iff h h' Xp Xm).mpr ⟨hsq,hsq'⟩⟩
    exact ⟨hra.mp hh.1,hra'.mp hh'.1,hf,hf',hi⟩
  · rintro ⟨ha,ha',hf,hf',he,hl,hsq⟩
    obtain ⟨hi,hi',hsquares⟩ := (integral_squares_iff_event_lines K h h' hs hs' hroot
      hlarge hlarge' hu hu' hle hsame hx hV Xp Xm
      (currentGiantUnits_of_frequencyGiantCoprime _ hf)
      (currentGiantUnits_of_frequencyGiantCoprime _ hf')).mpr ⟨he,hl,hsq⟩
    have hp := (pairNumeratorSquares_iff h h' Xp Xm).mp hsquares
    exact ⟨⟨hra.mpr ha,hi,hag.mpr ⟨hf,hp.1,ho.pivotOutsideCoprime⟩⟩,
      ⟨hra'.mpr ha',hi',hag'.mpr ⟨hf',hp.2,ho'.pivotOutsideCoprime⟩⟩⟩

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI
