import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationB
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationBlocks
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationIndependent

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistoryCRTIntegration HistoryFrequencyResidues

theorem pairedGuardIndicator_eq_blocks (K : ℕ) {l : ℕ}
    {V : ℕ → ℕ} {outside : List ℕ} (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hsmall : h.root.small.Perm k.root.small) (Xp Xm : ℤ) :
    guardIndicator (FiniteFactoredResidueGuard K h k hs ks Xp Xm) =
      rootResidueIndicator h (Xp,Xm) * pairedFrequencyResidueIndicator K h k (Xp,Xm) *
        primeResidueIndicatorB h k hs ks (Xp,Xm) := by
  have ha := rootSmallUnits_pair_iff_isUnit h k hsmall Xp Xm
  have hb := ownPrimeLines_and_squareLines_iff_finiteB h k hs ks Xp Xm
  have he : FiniteFactoredResidueGuard K h k hs ks Xp Xm ↔
      (((IsUnit (Xp:ZMod (rootModulus h)) ∧ IsUnit (Xm:ZMod (rootModulus h))) ∧
        (pairedFiniteFrequencyUnits K h k (Xp,Xm) ∧
          pairedFiniteLeafAdmissible K h k (Xp,Xm))) ∧
        finiteOwnPrimeLinesB h k hs ks (Xp,Xm)) := by
    rw [←ha,←hb]
    unfold FiniteFactoredResidueGuard
    tauto
  rw [propext he,guardIndicator_and,guardIndicator_and]
  rfl

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI
