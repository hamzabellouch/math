import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationBlocks
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorCRT

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistorySignedDecode HistorySignedNumerators HistorySupportReduction
open HistorySignedSupportReduction HistorySignedSpectator HistorySignedResidues
open HistoryPairPattern HistoryPairRows HistoryFrequencyResidues HistoryCRTIntegration
open HistoryRepresentativeSourceSeparation HistorySignedSpectatorCRT

def ringPairReduction {n M : ℕ} (hd : n∣M) (z : ZMod M×ZMod M) : ZMod n×ZMod n :=
  (ZMod.castHom hd (ZMod n) z.1,ZMod.castHom hd (ZMod n) z.2)

@[simp] theorem ringPairReduction_intCast {n M : ℕ} (hd : n∣M) (Xp Xm : ℤ) :
    ringPairReduction hd ((Xp:ZMod M),(Xm:ZMod M))=((Xp:ZMod n),(Xm:ZMod n)) := by
  simp only [ringPairReduction,map_intCast]

theorem liftedResidueTest_intCast_eq_four_blocks
    (K : ℕ) {l : ℕ} (h h' : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (hroot : RootGiantsAgree h h') (hsmall : h.root.small.Perm h'.root.small)
    (hlarge : LargePrimes V h) (hlarge' : LargePrimes V h')
    (hu : FrequencyUnits (pairedFrequencyProduct h h') h)
    (hu' : FrequencyUnits (pairedFrequencyProduct h h') h') (hle : l≤K)
    (had : PairAdmissible h h' outside)
    (hV : ∀i : Occurrences h h',∀j≤l,V j<(slot h h' i).value)
    (g : (q : ℕ) → ZMod q → ℂ)
    (hprime : ∀q∈outside,q.Prime) (hg : ∀q∈outside,g q 0=0)
    [NeZero (pairModulus h h' outside)] (M : ℕ)
    (hd : pairModulus h h' outside∣M) (hA : rootModulus h∣M)
    (hD : outside.prod∣M) (hR : frequencyModulus h h' (K+2)∣M)
    (hB : representativeModulus h h'∣M)
    (Xp Xm : ℤ) :
    let z : ZMod M×ZMod M := (Xp,Xm)
    liftedResidueTest g V outside h h' M hd z =
      rootResidueIndicator h (ringPairReduction hA z) *
        residuePairSpectator g outside outside.prod h h' (ringPairReduction hD z) *
        independentFrequencyResidueIndicator K h h' (ringPairReduction hR z) *
        primeResidueIndicatorB h h' hs hs' (ringPairReduction hB z) := by
  classical
  dsimp only
  simp only [ringPairReduction_intCast]
  rw [liftedResidueTest_intCast_independent_factored K h h' hs hs' hroot
    hlarge hlarge' hu hu' hle had.2.2.1 hV g hprime hg M hd Xp Xm]
  have he : (if IndependentFactoredResidueGuard K h h' hs hs' Xp Xm then
      pairSpectator g outside (rebuild h Xp Xm) (rebuild h' Xp Xm) else 0) =
      guardIndicator (IndependentFactoredResidueGuard K h h' hs hs' Xp Xm) *
        residuePairSpectator g outside outside.prod h h' (Xp,Xm) := by
    by_cases hi : IndependentFactoredResidueGuard K h h' hs hs' Xp Xm
    · have hint := (independent_integral_frequency_iff_finite K h h' hs hs' hroot
        hlarge hlarge' hu hu' hle had.2.2.1 hV Xp Xm).mpr
        ⟨hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2.1⟩
      simp only [ite_eq_left hi,guardIndicator,one_mul]
      exact (residuePairSpectator_intCast_actual h h' hs hs' had g Xp Xm hint.1 hint.2.1).symm
    · simp only [ite_eq_right hi,guardIndicator,zero_mul]
  rw [he,independentGuardIndicator_eq_blocks K h h' hs hs' hsmall Xp Xm]
  ring

theorem liftedResidueTest_eq_four_blocks
    (K : ℕ) {l : ℕ} (h h' : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (hroot : RootGiantsAgree h h') (hsmall : h.root.small.Perm h'.root.small)
    (hlarge : LargePrimes V h) (hlarge' : LargePrimes V h')
    (hu : FrequencyUnits (pairedFrequencyProduct h h') h)
    (hu' : FrequencyUnits (pairedFrequencyProduct h h') h') (hle : l≤K)
    (had : PairAdmissible h h' outside)
    (hV : ∀i : Occurrences h h',∀j≤l,V j<(slot h h' i).value)
    (g : (q : ℕ) → ZMod q → ℂ)
    (hprime : ∀q∈outside,q.Prime) (hg : ∀q∈outside,g q 0=0)
    [NeZero (pairModulus h h' outside)] (M : ℕ)
    (hd : pairModulus h h' outside∣M) (hA : rootModulus h∣M)
    (hD : outside.prod∣M) (hR : frequencyModulus h h' (K+2)∣M)
    (hB : representativeModulus h h'∣M)
    [NeZero M] (z : ZMod M×ZMod M) :
    liftedResidueTest g V outside h h' M hd z =
      rootResidueIndicator h (ringPairReduction hA z) *
        residuePairSpectator g outside outside.prod h h' (ringPairReduction hD z) *
        independentFrequencyResidueIndicator K h h' (ringPairReduction hR z) *
        primeResidueIndicatorB h h' hs hs' (ringPairReduction hB z) := by
  simpa only [Int.cast_natCast,ZMod.natCast_zmod_val,Prod.mk.eta] using
    liftedResidueTest_intCast_eq_four_blocks K h h' hs hs' hroot hsmall
      hlarge hlarge' hu hu' hle had hV g hprime hg M hd hA hD hR hB
      (z.1.val:ℤ) (z.2.val:ℤ)

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI
