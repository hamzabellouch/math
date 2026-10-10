import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorization
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesLift

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistorySignedDecode HistorySignedNumerators HistorySupportReduction
open HistorySignedSupportReduction HistorySignedSpectator HistorySignedResidues
open HistoryPairPattern HistoryPairRows HistoryFrequencyResidues

theorem signed_pair_mask_eq_factored
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
    (hprime : ∀q∈outside,q.Prime) (hg : ∀q∈outside,g q 0=0) (Xp Xm : ℤ) :
    (show ℂ from by
      classical
      exact if (ResidueGuarded V outside (rebuild h Xp Xm) ∧
          ResidueGuarded V outside (rebuild h' Xp Xm)) then
        pairSpectator g outside (rebuild h Xp Xm) (rebuild h' Xp Xm) else 0) =
    (by classical exact if FactoredResidueGuard K h h' hs hs' Xp Xm then
        pairSpectator g outside (rebuild h Xp Xm) (rebuild h' Xp Xm) else 0) := by
  classical
  by_cases hz : pairSpectator g outside (rebuild h Xp Xm) (rebuild h' Xp Xm)=0
  · simp only [hz,ite_self]
  · obtain ⟨ho,ho'⟩ := pairSpectator_nonzero_rebuild_outsideUnits g outside hprime hg
      h h' Xp Xm Xp Xm hz
    simp only [residueGuarded_pair_iff_factored_of_outsideUnits K h h' hs hs' hroot
      hlarge hlarge' hu hu' hle hsame hx hV Xp Xm ho ho']

theorem residueTest_intCast_factored
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
    [NeZero (pairModulus h h' outside)] (Xp Xm : ℤ) :
    residueTest g V outside h h' ((Xp:ZMod (pairModulus h h' outside)),
      (Xm:ZMod (pairModulus h h' outside))) =
    (by classical exact if FactoredResidueGuard K h h' hs hs' Xp Xm then
      pairSpectator g outside (rebuild h Xp Xm) (rebuild h' Xp Xm) else 0) := by
  rw [residueTest_intCast g h h' hs hs' Xp Xm]
  exact signed_pair_mask_eq_factored K h h' hs hs' hroot hlarge hlarge' hu hu' hle
    hsame hx hV g hprime hg Xp Xm

theorem liftedResidueTest_intCast_factored
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
    (by classical exact if FactoredResidueGuard K h h' hs hs' Xp Xm then
      pairSpectator g outside (rebuild h Xp Xm) (rebuild h' Xp Xm) else 0) := by
  rw [liftedResidueTest_intCast g h h' hs hs' M hd Xp Xm]
  exact signed_pair_mask_eq_factored K h h' hs hs' hroot hlarge hlarge' hu hu' hle
    hsame hx hV g hprime hg Xp Xm

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI
