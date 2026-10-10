import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyGuardContextCanonical
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyIndependentPair
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationRootUnits

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistoryCRTIntegration HistoryFrequencyResidues

def guardIndicator (P : Prop) : ℂ := by classical exact if P then 1 else 0

theorem guardIndicator_and (P Q : Prop) :
    guardIndicator (P∧Q)=guardIndicator P*guardIndicator Q := by
  classical
  by_cases hp:P <;> by_cases hq:Q <;> simp [guardIndicator,hp,hq]

def rootResidueIndicator {l : ℕ} (h : History l)
    (z : ZMod (rootModulus h) × ZMod (rootModulus h)) : ℂ :=
  guardIndicator (IsUnit z.1 ∧ IsUnit z.2)

def independentFrequencyResidueIndicator (K : ℕ) {l : ℕ} (h k : History l)
    (z : ZMod (frequencyModulus h k (K+2)) × ZMod (frequencyModulus h k (K+2))) : ℂ :=
  guardIndicator (independentFiniteFrequencyUnits K h k z ∧ independentFiniteLeafAdmissible K h k z)

def pairedFrequencyResidueIndicator (K : ℕ) {l : ℕ} (h k : History l)
    (z : ZMod (frequencyModulus h k (K+2)) × ZMod (frequencyModulus h k (K+2))) : ℂ :=
  guardIndicator (pairedFiniteFrequencyUnits K h k z ∧ pairedFiniteLeafAdmissible K h k z)

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI
