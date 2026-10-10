import OAI.NumberTheory.Ostmann.Characters.MixedFlatnessSpectatorFacade
import OAI.NumberTheory.Ostmann.Construction.InitialEtaConstructionInterface

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open Filter
namespace Ostmann.Construction

theorem initial_amplitude_construction_actual : ∃ δ : ℝ, 0 < δ ∧
    ∀ (d : Decomposition) (Bs BD Bz : ℝ), 200 ≤ Bs → ∀ (k : ℕ), 0 < k →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop,
        ∃ (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
          (hZ : 0 < harmonicPrimeMass P),
          P = Characters.mixedSpectatorPrimes d ε L ∧
          L / 5000 ≤ harmonicPrimeMass P ∧
          (L / 5000) * Real.exp (Real.exp ((1 / 2000 : ℝ) * L)) ≤ (P.card : ℝ) ∧
          (∀ p ∈ P, Real.exp ((1 / 2000 : ℝ) * L) ≤ Real.log (p : ℝ) ∧
            Real.log (p : ℝ) ≤ Real.exp ((1 / 1000 : ℝ) * L)) ∧
          (1 / 2 : ℝ) ≤ (harmonicPrimeSource P hP hZ).law.mean
            (fun p => balancedPrimeIndicator d p) ∧
          (∀ p ∈ P, Supply.balancedDensity d p ∧ Characters.mixedPrimeBias d p < ε) ∧
          ∀ E : Finset ℕ, E.card ≤ 2 →
            ∃ C : InitialSourceChoice d Bs BD Bz k L E,
              C.favorable ⊆ Supply.nonsparsePrimes d δ L ∧
              Real.exp ((1 / 20 : ℝ) * L) ≤ C.blockBase ∧
              C.blockBase + favorableBlockWidth L ≤ Real.exp ((9 / 10 : ℝ) * L) ∧
              C.blockBase - 2 < (C.giantCenter : ℝ) ∧
              (C.giantCenter : ℝ) < C.blockBase + favorableBlockWidth L + 2 ∧
              |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L / 16 ∧
              |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L / 16 ∧
              C.CrossRoleSeparation (harmonicPrimeSource P hP hZ) ∧
              Real.sqrt C.scale * Real.exp (-27 * (Conclusion.bulkSize k L : ℝ)) ≤
                C.statistic (harmonicPrimeSource P hP hZ) ∧
              ∀ G : ℝ, Real.exp (-28 * (Conclusion.bulkSize k L : ℝ)) ≤
                ‖decompositionAmplitude d C.favorable C.sources
                  (Conclusion.frequencyBound Bs BD Bz k L)
                  C.giant (harmonicPrimeSource P hP hZ) C.scale G
                  (Conclusion.bulkSize k L / 2) (Conclusion.bulkSize k L / 2)
                  k C.bulkBin C.spectatorBin 0‖ := by
  obtain ⟨δ, hδ, hbuild⟩ := initial_amplitude_construction_interface
  refine ⟨δ, hδ, ?_⟩
  intro d Bs BD Bz hBs k hk ε hε
  filter_upwards [hbuild d Bs BD Bz hBs k hk,
    Characters.eventually_exists_actual_mixed_spectator_facade d ε hε] with L hbuild hspectator
  obtain ⟨P, hP, hZ, hPeq, hmass, hcard, hband, hbalanced, hflat⟩ := hspectator
  refine ⟨P, hP, hZ, hPeq, hmass, hcard, hband, hbalanced, hflat, ?_⟩
  intro E hE
  exact hbuild E hE P hP hZ hmass hband hbalanced

end Ostmann.Construction

end

end OAI
