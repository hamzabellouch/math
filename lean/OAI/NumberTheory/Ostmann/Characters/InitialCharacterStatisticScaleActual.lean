import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScale
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleGeometry

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.InitialCharacterScale
open Construction Preliminaries Filter

theorem initial_amplitude_exponential_at_actual_scales
    {ρ c₀ C H δ CI Ccell α : ℝ} (hρ : 0 < ρ) (hc₀ : 0 < c₀)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hCI : 0 ≤ CI) (hCell : 0 ≤ Ccell) (hα : 0 < α) (Cw : ℝ) :
    ∀ᶠ k : ℕ in atTop, ∀ BD : ℝ,
      gapThreshold (positiveRate Cw CI) ρ (2*C) H ≤ BD →
      ∀ DE DP DH : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ (Q b nc : ℕ), (nc : ℝ) ≤ maxCells Ccell k → b = wordSize k L+1+nc →
      ∀ (E : Fin b → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i)),
      ∀ (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
        (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ),
      (∀ i, ∀ p ∈ E i, χ i p.val ≠ 1) → (∀ i, ∀ p ∈ E i, ‖z i p.val‖ ≤ 1) →
      ∀ B : (Fin b → PrimeUpTo Q) → ℝ, (∀ w, 0 ≤ B w ∧ B w ≤ 1) →
      ∀ (S : Finset ℤ) (X : ℝ), 0 < X →
      (∀ x ∈ S, |(x : ℝ)/X| ≤ 1) →
      (∀ x ∈ S, Real.exp (-Cw*(wordSize k L : ℝ))*δ^nc ≤
        ‖initialCharacterMean E hE χ a z B x‖) →
      Real.exp (-Cw*(wordSize k L : ℝ)-CI*maxCells Ccell k*L-DE) ≤
        (S.card : ℝ)/Real.sqrt X →
      (∏ i, (primeShellMass (E i))⁻¹) ≤
        (1/(ρ*L))^(wordSize k L)/c₀*Real.exp (C*maxCells Ccell k*L) →
      primeShellMass (Finset.univ.biUnion E) ≤ H*L+DH →
      (∀ i, ∀ p ∈ E i, Real.exp (Real.exp (α*L)) ≤ (p.val : ℝ)) →
      (∀ w : Fin (b+b) → PrimeUpTo Q,
        (∀ i, w i ∈ characterDoubleShell E i) → characterDoubleMask B w ≠ 0 →
        X*Real.exp (initialGap BD k L-DP) ≤ (characterTupleProduct w : ℝ) ∧
        (characterTupleProduct w : ℝ) ≤ X*Real.exp (initialGap BD k L+DP)) →
      Real.exp (-amplitudeRate Cw CI*(wordSize k L : ℝ)) ≤
      ‖initialCharacterAmplitude (characterDoubleShell E) (characterDoubleShell_positive E hE)
        (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase z)
        (characterDoubleMask B) X‖ := by
  filter_upwards [eventually_maxCells_le_depthScale Ccell] with k hN
  intro BD hBD DE DP DH
  have hN0 : 0 ≤ maxCells Ccell k := by unfold maxCells; positivity
  filter_upwards [initial_amplitude_exponential_of_source_bounds hρ hc₀ hC hH hδ hδone
    hCI hN0 Cw k hN BD DE DP DH hBD,
    repeated_period_small_eventually hα BD DP k] with L hmain hperiod
  intro Q b nc hnc hb E hE χ a z hχ hz B hB S X hX hS hgood hcount hNorm hUnion hmin hwindow
  exact hmain Q b nc hnc hb E hE χ a z hχ hz B hB S X
    (Real.exp (Real.exp (α*L))) (X*Real.exp (initialGap BD k L-DP))
    (X*Real.exp (initialGap BD k L+DP)) hX (Real.exp_pos _)
    (mul_pos hX (Real.exp_pos _)) hS hgood hcount hNorm hUnion le_rfl hmin hwindow (hperiod X hX)

end Ostmann.Characters.InitialCharacterScale

end

end OAI
