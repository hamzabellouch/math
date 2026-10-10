import OAI.NumberTheory.Ostmann.Characters.MixedFlatnessSpectatorSelection
import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonObstruction
import OAI.NumberTheory.Ostmann.Conclusion.LowLevelBadPairs
import OAI.NumberTheory.Ostmann.Conclusion.Scales
import OAI.NumberTheory.Ostmann.Conclusion.SelectedPermutation
import OAI.NumberTheory.Ostmann.Construction.DiagonalSingleEnergy
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalGoodNormalizerBasic
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalSplit
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparation
import OAI.NumberTheory.Ostmann.Supply.Statement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open Construction Filter

theorem exists_actual_comparison_obstruction_interface : ∃ δ : ℝ, 0 < δ ∧
    ∀ (d : Decomposition) (Cs Ccov : ℝ) (kmin : ℕ),
    ∃ BD Bz : ℝ, 0 ≤ BD ∧ 9 ≤ Bz ∧ 200+Cs+105 ≤ BD ∧
    ∃ k : ℕ, max 2 kmin ≤ k ∧ finalRate BD 200 Bz (Ccov+2) k < -66 ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop,
      ∃ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hZ : 0 < harmonicPrimeMass P),
        P = Characters.mixedSpectatorPrimes d ε L ∧
        L/5000 ≤ harmonicPrimeMass P ∧
        (L/5000)*Real.exp (Real.exp ((1/2000:ℝ)*L)) ≤ (P.card:ℝ) ∧
        (∀ p ∈ P, Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℝ) ∧
          Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) ∧
        (1/2:ℝ) ≤ (harmonicPrimeSource P hP hZ).law.mean (fun p => balancedPrimeIndicator d p) ∧
        (∀ p ∈ P, Supply.balancedDensity d p ∧ Characters.mixedPrimeBias d p < ε) ∧
      ∀ (E : Finset ℕ), E.card ≤ 2 →
      ∃ C : InitialSourceChoice d 200 BD Bz k L E,
        C.favorable ⊆ Supply.nonsparsePrimes d δ L ∧
        Real.exp ((1/20:ℝ)*L) ≤ C.blockBase ∧
        C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) ∧
        C.blockBase-2 < (C.giantCenter:ℝ) ∧
        (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 ∧
        |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 ∧
        |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 ∧
        C.CrossRoleSeparation (harmonicPrimeSource P hP hZ) ∧
        ¬ ((∀ j < k, C.selectedDiagonalSingleEnergy (harmonicPrimeSource P hP hZ)
            (bulkSize k L/2) C.scale j ≤
          Real.exp ((2:ℝ)^j*(initialGap 200 k L+Cs*(bulkSize k L:ℝ)))) ∧
        (∀ j < k, ∀ e, InitialSourceChoice.diagonalGoodPermutation (2*(bulkSize k L/2)) k j e →
          ‖C.selectedDiagonalCovariance (harmonicPrimeSource P hP hZ) (bulkSize k L/2) C.scale j e‖ ≤
          Real.exp (-(selectedDiagonalGoodRate k+67*(2:ℝ)^k)*(bulkSize k L:ℝ))) ∧
        (∀ a b, TransferBadArrangement (a⁻¹*b) →
          selectedCovariance C (harmonicPrimeSource P hP hZ) (bulkSize k L/2) k a b ≤
            Real.exp ((2:ℝ)^k*(initialGap 200 k L+Ccov*(bulkSize k L:ℝ))+(bulkSize k L:ℝ))) ∧
        (∀ a b, ¬TransferBadArrangement (a⁻¹*b) →
          selectedCovariance C (harmonicPrimeSource P hP hZ) (bulkSize k L/2) k a b ≤
            Real.exp (-(frequencyBudget 200 BD Bz k L k+65*(2:ℝ)^k*(bulkSize k L:ℝ))))) :=
  exists_actual_comparison_obstruction

end Ostmann.Conclusion

end

end OAI
