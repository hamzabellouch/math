import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseTests

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistoryBulkFrequencyTransport HistoryFrequencyResidues
open HistorySignedResidueFactorization HistoryPairedFrequencyAverage

theorem residuePairTransport_intCast (K : ℕ) {R S : ℕ} (h : R=S) (Xp Xm : ℤ) :
    residuePairTransport K h ((Xp:ZMod (S^(K+2))),(Xm:ZMod (S^(K+2))))=
      ((Xp:ZMod (R^(K+2))),(Xm:ZMod (R^(K+2)))) := by
  subst S
  rfl

theorem pairedIndicator_eq_reference_intCast {l : ℕ} {h g h' g' : History l}
    (ha : SameFrequencyData h g) (hb : SameFrequencyData h' g') (K : ℕ) (Xp Xm : ℤ) :
    pairedFrequencyResidueIndicator K h h' (Xp,Xm)=
      leafIndicator K (pairedFrequencyProduct g g') (frequencySchedule g g')
        (fixedFactorSchedule g g') g g' []
        (l,initialResidueGiants K (pairedFrequencyProduct g g') (Xp,Xm),
          initialResidueGiants K (pairedFrequencyProduct g g') (Xp,Xm))
        (frequencyLeaves ((pairedFrequencyProduct g g')^(K+2)) h) := by
  have he := pairedIndicator_eq_reference ha hb K
    ((Xp:ZMod ((pairedFrequencyProduct g g')^(K+2))),
      (Xm:ZMod ((pairedFrequencyProduct g g')^(K+2))))
  erw [residuePairTransport_intCast] at he
  exact he

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
