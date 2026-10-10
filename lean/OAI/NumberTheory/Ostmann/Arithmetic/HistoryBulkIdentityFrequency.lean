import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIdentityFrequencyIndicator
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIdentityFrequencySchedules

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIdentityFrequency
open Construction Characters FrequencyExposure BinaryExposure HistoryFrequencyResidues
open HistoryPairedFrequencyAverage HistoryBulkResidueNormSum

theorem independentRTest_identity (K : ℕ) {l m : ℕ} (h k : History l)
    (z : ZMod ((pairedFrequencyProduct h k)^(K+2)) ×
      ZMod ((pairedFrequencyProduct h k)^(K+2)))
    (x : Fin (2^l)×Fin m → (ZMod ((pairedFrequencyProduct h k)^(K+2)))ˣ) :
    independentRTest K h k 1 z x = canonicalRTest K h k z x := by
  unfold canonicalRTest
  rw [leafIndicator_split]
  simp only [frequencySchedule]
  erw [leftData_frequencyScheduleAux,rightData_frequencyScheduleAux,
    leftFactors_fixedFactorSchedule,rightFactors_fixedFactorSchedule]
  simp only [leftContext,rightContext]
  rfl

end Ostmann.Arithmetic.HistoryBulkIdentityFrequency

end

end OAI
