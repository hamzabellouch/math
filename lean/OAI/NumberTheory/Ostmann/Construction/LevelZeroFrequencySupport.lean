import OAI.NumberTheory.Ostmann.Construction.InitialEtaPeriod
import OAI.NumberTheory.Ostmann.Construction.InitialEtaStateProducts
import OAI.NumberTheory.Ostmann.Construction.LevelZeroFrequencyReserveGrowth

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction.InitialEta
open Filter

theorem initial_scale_pos {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ}
    {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k L E) : 0 < C.scale := by
  unfold InitialSourceChoice.scale giantWindowScale
  exact Nat.ceil_pos.mpr (Real.exp_pos _)

theorem eventually_initial_tuplePeriod_frequency (Bs BD Bz : ℝ) (hBs : 0≤Bs)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ {d : Decomposition} {E : Finset ℕ}
      (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
      (x : JointSample C.giant C.bulk spectator C.auxiliary
        (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)),
      (jointPrior C.giant C.bulk spectator C.auxiliary
        (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)).mass x≠0 →
      tupleBins C.bulkBin C.spectatorBin x≠0 →
      (tuplePeriod x:ℝ)/(4*(C.scale:ℝ))≤(Conclusion.frequencyBound Bs BD Bz k L 0:ℝ) := by
  filter_upwards [eventually_levelZero_nat_period_frequency Bs BD Bz hBs hk] with L hL
  intro d E C spectator x hm hb
  apply hL (tuplePeriod x) C.scale (by exact_mod_cast initial_scale_pos C)
  have hh := (abs_le.mp (initial_tuplePeriod_log_support C spectator x hm hb)).2
  unfold levelZeroSupportWidth
  linarith

theorem eventually_initial_statePeriod_frequency (Bs BD Bz : ℝ) (hBs : 0≤Bs)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ {d : Decomposition} {E : Finset ℕ}
      (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
      (x : JointSample C.giant C.bulk spectator C.auxiliary
        (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)) (freq : ℤ),
      (jointPrior C.giant C.bulk spectator C.auxiliary
        (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)).mass x≠0 →
      tupleBins C.bulkBin C.spectatorBin x≠0 →
      ((outsideProduct (jointOutside x)*(jointState x freq).product:ℕ):ℝ)/(4*(C.scale:ℝ))≤
        (Conclusion.frequencyBound Bs BD Bz k L 0:ℝ) := by
  filter_upwards [eventually_initial_tuplePeriod_frequency Bs BD Bz hBs hk] with L hL
  intro d E C spectator x freq hm hb
  rw [jointState_period]
  exact hL C spectator x hm hb

end Ostmann.Construction.InitialEta

end

end OAI
