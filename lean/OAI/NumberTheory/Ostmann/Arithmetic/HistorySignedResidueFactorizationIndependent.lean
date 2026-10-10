import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyIndependentPair
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationStatic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesLift

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistorySignedDecode HistorySignedNumerators HistorySupportReduction
open HistorySignedSupportReduction HistorySignedSpectator HistorySignedResidues
open HistoryPairPattern HistoryPairRows HistoryFrequencyResidues

def IndependentFactoredResidueGuard (K : ℕ) {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h h' : History l) (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (Xp Xm : ℤ) : Prop :=
  RootSmallUnits h Xp Xm ∧ RootSmallUnits h' Xp Xm ∧
    independentFiniteFrequencyUnits K h h' (Xp,Xm) ∧ independentFiniteLeafAdmissible K h h' (Xp,Xm) ∧
    OwnPrimeLines h h' hs hs' Xp Xm ∧ OwnPrimeSquareLines h h' hs hs' Xp Xm

theorem residueGuarded_pair_iff_independent_of_outsideUnits
    (K : ℕ) {l : ℕ} (h h' : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (hroot : RootGiantsAgree h h')
    (hlarge : LargePrimes V h) (hlarge' : LargePrimes V h')
    (hu : FrequencyUnits (pairedFrequencyProduct h h') h)
    (hu' : FrequencyUnits (pairedFrequencyProduct h h') h') (hle : l≤K)
    (hx : ∀i : Occurrences h h', AncestorUnits h h'
      (fun j => (pairSample h h' j:ZMod (slot h h' i).value)) i)
    (hV : ∀i : Occurrences h h',∀j≤l,V j<(slot h h' i).value)
    (Xp Xm : ℤ) (ho : OutsideUnits outside (rebuild h Xp Xm))
    (ho' : OutsideUnits outside (rebuild h' Xp Xm)) :
    (ResidueGuarded V outside (rebuild h Xp Xm) ∧
      ResidueGuarded V outside (rebuild h' Xp Xm)) ↔
      IndependentFactoredResidueGuard K h h' hs hs' Xp Xm := by
  rw [residueGuarded_pair_iff_static h h' hs hs' hlarge hlarge' Xp Xm ho ho']
  have hc := independent_integral_frequency_iff_finite K h h' hs hs' hroot
    hlarge hlarge' hu hu' hle hx hV Xp Xm
  constructor
  · rintro ⟨ha,ha',hi,hi',hf,hf',hsq⟩
    obtain ⟨hknown,hevent,hlines⟩ := hc.mp ⟨hi,hi',hf,hf'⟩
    have hsquares := (pairNumeratorSquares_iff_ownPrimeSquareLines h h' hs hs'
      hroot Xp Xm hi hi' hx hV).mp hsq
    exact ⟨ha,ha',hknown,hevent,hlines,hsquares⟩
  · rintro ⟨ha,ha',hknown,hevent,hlines,hsq⟩
    obtain ⟨hi,hi',hf,hf'⟩ := hc.mpr ⟨hknown,hevent,hlines⟩
    have hsquares := (pairNumeratorSquares_iff_ownPrimeSquareLines h h' hs hs'
      hroot Xp Xm hi hi' hx hV).mpr hsq
    exact ⟨ha,ha',hi,hi',hf,hf',hsquares⟩

theorem liftedResidueTest_intCast_independent_factored
    (K : ℕ) {l : ℕ} (h h' : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (hroot : RootGiantsAgree h h')
    (hlarge : LargePrimes V h) (hlarge' : LargePrimes V h')
    (hu : FrequencyUnits (pairedFrequencyProduct h h') h)
    (hu' : FrequencyUnits (pairedFrequencyProduct h h') h') (hle : l≤K)
    (hx : ∀i : Occurrences h h', AncestorUnits h h'
      (fun j => (pairSample h h' j:ZMod (slot h h' i).value)) i)
    (hV : ∀i : Occurrences h h',∀j≤l,V j<(slot h h' i).value)
    (g : (q : ℕ) → ZMod q → ℂ)
    (hprime : ∀q∈outside,q.Prime) (hg : ∀q∈outside,g q 0=0)
    [NeZero (pairModulus h h' outside)] (M : ℕ) (hd : pairModulus h h' outside∣M)
    (Xp Xm : ℤ) :
    liftedResidueTest g V outside h h' M hd ((Xp:ZMod M),(Xm:ZMod M)) =
    (by classical exact if IndependentFactoredResidueGuard K h h' hs hs' Xp Xm then
      pairSpectator g outside (rebuild h Xp Xm) (rebuild h' Xp Xm) else 0) := by
  classical
  rw [liftedResidueTest_intCast g h h' hs hs' M hd Xp Xm]
  by_cases hz : pairSpectator g outside (rebuild h Xp Xm) (rebuild h' Xp Xm)=0
  · simp only [hz,ite_self]
  · obtain ⟨ho,ho'⟩ := pairSpectator_nonzero_rebuild_outsideUnits g outside hprime hg
      h h' Xp Xm Xp Xm hz
    have he := residueGuarded_pair_iff_independent_of_outsideUnits K h h' hs hs' hroot
      hlarge hlarge' hu hu' hle hx hV Xp Xm ho ho'
    by_cases ha : ResidueGuarded V outside (rebuild h Xp Xm) ∧
        ResidueGuarded V outside (rebuild h' Xp Xm)
    · simp only [ite_eq_left ha,ite_eq_left (he.mp ha)]
    · simp only [ite_eq_right ha,ite_eq_right (fun hb=>ha (he.mpr hb))]

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI
