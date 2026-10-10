import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyGuardContextCanonical
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationMask

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistorySignedDecode HistorySignedNumerators HistorySupportReduction
open HistorySignedSupportReduction HistorySignedSpectator HistorySignedResidues
open HistoryPairPattern HistoryPairRows HistoryFrequencyResidues

def FiniteFactoredResidueGuard (K : ℕ) {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h h' : History l) (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (Xp Xm : ℤ) : Prop :=
  RootSmallUnits h Xp Xm ∧ RootSmallUnits h' Xp Xm ∧
    pairedFiniteFrequencyUnits K h h' (Xp,Xm) ∧ pairedFiniteLeafAdmissible K h h' (Xp,Xm) ∧
    OwnPrimeLines h h' hs hs' Xp Xm ∧ OwnPrimeSquareLines h h' hs hs' Xp Xm

theorem factoredResidueGuard_iff_finite
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
    (Xp Xm : ℤ) :
    FactoredResidueGuard K h h' hs hs' Xp Xm ↔
      FiniteFactoredResidueGuard K h h' hs hs' Xp Xm := by
  have hfinite := integral_frequency_iff_finite_event_lines K h h' hs hs' hroot
    hlarge hlarge' hu hu' hle hsame hx hV Xp Xm
  constructor
  · rintro ⟨ha,ha',hf,hf',he,hl,hsq⟩
    have hi := pair_integralGuard_of_canonical_event_lines K h h' hs hs' hroot
      hlarge hlarge' hu hu' hle hsame hx hV Xp Xm
      (currentGiantUnits_of_frequencyGiantCoprime _ hf)
      (currentGiantUnits_of_frequencyGiantCoprime _ hf') he hl
    obtain ⟨hk,he',hl'⟩ := hfinite.mp ⟨hi.1,hi.2,hf,hf'⟩
    exact ⟨ha,ha',hk,he',hl',hsq⟩
  · rintro ⟨ha,ha',hk,he,hl,hsq⟩
    obtain ⟨hi,hi',hf,hf'⟩ := hfinite.mpr ⟨hk,he,hl⟩
    have hh := (pair_integralGuard_iff_event_lines K h h' hs hs' hroot
      hlarge hlarge' hu hu' hle hsame hx hV Xp Xm
      (currentGiantUnits_of_frequencyGiantCoprime _ hf)
      (currentGiantUnits_of_frequencyGiantCoprime _ hf')).mp ⟨hi,hi'⟩
    exact ⟨ha,ha',hf,hf',hh.1,hh.2,hsq⟩

theorem liftedResidueTest_intCast_finite_factored
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
    (g : (q : ℕ) → ZMod q → ℂ)
    (hprime : ∀q∈outside,q.Prime) (hg : ∀q∈outside,g q 0=0)
    [NeZero (pairModulus h h' outside)] (M : ℕ) (hd : pairModulus h h' outside∣M)
    (Xp Xm : ℤ) :
    liftedResidueTest g V outside h h' M hd ((Xp:ZMod M),(Xm:ZMod M)) =
    (by classical exact if FiniteFactoredResidueGuard K h h' hs hs' Xp Xm then
      pairSpectator g outside (rebuild h Xp Xm) (rebuild h' Xp Xm) else 0) := by
  rw [liftedResidueTest_intCast_factored K h h' hs hs' hroot hlarge hlarge' hu hu'
    hle hsame hx hV g hprime hg M hd Xp Xm]
  classical
  have he := factoredResidueGuard_iff_finite K h h' hs hs' hroot hlarge hlarge' hu hu'
    hle hsame hx hV Xp Xm
  by_cases ha : FactoredResidueGuard K h h' hs hs' Xp Xm
  · simp only [ite_eq_left ha,ite_eq_left (he.mp ha)]
  · simp only [ite_eq_right ha,ite_eq_right (fun hb=>ha (he.mpr hb))]

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI
