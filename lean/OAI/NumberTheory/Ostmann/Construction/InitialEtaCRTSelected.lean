import OAI.NumberTheory.Ostmann.Construction.InitialEtaCRT
import OAI.NumberTheory.Ostmann.Construction.InitialEtaExpansion
import OAI.NumberTheory.Ostmann.Construction.LevelZeroFrequencySupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction.InitialEta
open Filter

theorem eventually_initial_distinct_eq_amplitude (Bs BD Bz : ℝ) (hBs : 0 ≤ Bs)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ {d : Decomposition} {E : Finset ℕ}
      (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource) (G : ℝ),
      distinctContribution d C.favorable C.giant C.bulk spectator C.auxiliary
        (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)
        C.bulkBin C.spectatorBin C.scale =
      decompositionAmplitude d C.favorable C.sources (Conclusion.frequencyBound Bs BD Bz k L)
        C.giant spectator C.scale G (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)
        k C.bulkBin C.spectatorBin 0 := by
  filter_upwards [eventually_initial_tuplePeriod_frequency Bs BD Bz hBs hk] with L hL
  intro d E C spectator G
  exact distinctContribution_eq_decompositionAmplitude d C.favorable C.giant C.bulk spectator
    C.auxiliary (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)
    C.bulkBin C.spectatorBin (Conclusion.frequencyBound Bs BD Bz k L) C.scale G
    (by exact_mod_cast initial_scale_pos C)
    (fun x hm _ hb => hL C spectator x hm hb)

theorem eventually_initial_statistic_eq_amplitude_add_repeated
    (Bs BD Bz : ℝ) (hBs : 0 ≤ Bs) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ {d : Decomposition} {E : Finset ℕ}
      (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource) (G : ℝ),
      (C.statistic spectator : ℂ)/(Real.sqrt (C.scale:ℝ):ℂ) =
      decompositionAmplitude d C.favorable C.sources (Conclusion.frequencyBound Bs BD Bz k L)
        C.giant spectator C.scale G (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)
        k C.bulkBin C.spectatorBin 0 +
      repeatedContribution d C.favorable C.giant C.bulk spectator C.auxiliary
        (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)
        C.bulkBin C.spectatorBin C.scale := by
  filter_upwards [eventually_initial_distinct_eq_amplitude Bs BD Bz hBs hk] with L hL
  intro d E C spectator G
  have hh := statistic_eq_distinct_add_repeated d C.favorable C.giant C.bulk spectator
    C.auxiliary (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)
    C.bulkBin C.spectatorBin (X := (C.scale:ℝ)) (by exact_mod_cast initial_scale_pos C)
  rw [hL C spectator G] at hh
  exact hh

end Ostmann.Construction.InitialEta

end

end OAI
