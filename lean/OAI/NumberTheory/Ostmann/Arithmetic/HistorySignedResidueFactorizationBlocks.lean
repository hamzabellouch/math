import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationB
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationBlockDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationIndependent

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistoryCRTIntegration HistoryFrequencyResidues

def primeResidueIndicatorB {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ} (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (z : ZMod (representativeModulus h k) × ZMod (representativeModulus h k)) : ℂ :=
  guardIndicator (finiteOwnPrimeLinesB h k hs ks z)

theorem independentGuardIndicator_eq_blocks (K : ℕ) {l : ℕ}
    {V : ℕ → ℕ} {outside : List ℕ} (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hsmall : h.root.small.Perm k.root.small) (Xp Xm : ℤ) :
    guardIndicator (IndependentFactoredResidueGuard K h k hs ks Xp Xm) =
      rootResidueIndicator h (Xp,Xm) * independentFrequencyResidueIndicator K h k (Xp,Xm) *
        primeResidueIndicatorB h k hs ks (Xp,Xm) := by
  have ha := rootSmallUnits_pair_iff_isUnit h k hsmall Xp Xm
  have hb := ownPrimeLines_and_squareLines_iff_finiteB h k hs ks Xp Xm
  have he : IndependentFactoredResidueGuard K h k hs ks Xp Xm ↔
      (((IsUnit (Xp:ZMod (rootModulus h)) ∧ IsUnit (Xm:ZMod (rootModulus h))) ∧
        (independentFiniteFrequencyUnits K h k (Xp,Xm) ∧
          independentFiniteLeafAdmissible K h k (Xp,Xm))) ∧
        finiteOwnPrimeLinesB h k hs ks (Xp,Xm)) := by
    rw [←ha,←hb]
    unfold IndependentFactoredResidueGuard
    tauto
  rw [propext he,guardIndicator_and,guardIndicator_and]
  rfl

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI
