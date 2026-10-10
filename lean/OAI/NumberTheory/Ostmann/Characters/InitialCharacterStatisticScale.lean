import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleError
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScalePositive

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.InitialCharacterScale
open Construction Preliminaries Filter

theorem amplitudeRate_pos {Cw CI : ℝ} (hCw : 0 ≤ Cw) (hCI : 0 ≤ CI) :
    0 < amplitudeRate Cw CI := by unfold amplitudeRate positiveRate; linarith

theorem initial_amplitude_exponential_of_source_bounds
    {ρ c₀ C H δ CI N : ℝ} (hρ : 0 < ρ) (hc₀ : 0 < c₀)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hCI : 0 ≤ CI) (hN : 0 ≤ N) (Cw : ℝ) (k : ℕ) (hNz : N ≤ depthScale k)
    (BD DE DP DH : ℝ) (hBD : gapThreshold (positiveRate Cw CI) ρ (2*C) H ≤ BD) :
    ∀ᶠ L : ℝ in atTop, ∀ (Q b nc : ℕ), (nc : ℝ) ≤ N → b = wordSize k L+1+nc →
      ∀ (E : Fin b → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i)),
      ∀ (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
        (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ),
      (∀ i, ∀ p ∈ E i, χ i p.val ≠ 1) → (∀ i, ∀ p ∈ E i, ‖z i p.val‖ ≤ 1) →
      ∀ B : (Fin b → PrimeUpTo Q) → ℝ, (∀ w, 0 ≤ B w ∧ B w ≤ 1) →
      ∀ (S : Finset ℤ) (X R M₀ M₁ : ℝ), 0 < X → 0 < R → 0 < M₀ →
      (∀ x ∈ S, |(x : ℝ)/X| ≤ 1) →
      (∀ x ∈ S, Real.exp (-Cw*(wordSize k L : ℝ))*δ^nc ≤
        ‖initialCharacterMean E hE χ a z B x‖) →
      Real.exp (-Cw*(wordSize k L : ℝ)-CI*N*L-DE) ≤ (S.card : ℝ)/Real.sqrt X →
      (∏ i, (primeShellMass (E i))⁻¹) ≤
        (1/(ρ*L))^(wordSize k L)/c₀*Real.exp (C*N*L) →
      primeShellMass (Finset.univ.biUnion E) ≤ H*L+DH →
      X*Real.exp (initialGap BD k L-DP) ≤ M₀ →
      (∀ i, ∀ p ∈ E i, R ≤ (p.val : ℝ)) →
      (∀ w : Fin (b+b) → PrimeUpTo Q,
        (∀ i, w i ∈ characterDoubleShell E i) → characterDoubleMask B w ≠ 0 →
        M₀ ≤ (characterTupleProduct w : ℝ) ∧ (characterTupleProduct w : ℝ) ≤ M₁) →
      M₁ < 4*X*R →
      Real.exp (-amplitudeRate Cw CI*(wordSize k L : ℝ)) ≤
      ‖initialCharacterAmplitude (characterDoubleShell E) (characterDoubleShell_positive E hE)
        (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase z)
        (characterDoubleMask B) X‖ := by
  obtain ⟨cψ,hc,hamp⟩ := exists_initialCharacterAmplitude_constant
  filter_upwards [positive_scalar_lower hc hδ hδone hCI hN Cw DE k hNz,
    actual_repeated_error_small_eventually hρ hc₀ hC hH hBD k hNz DP DH,
    (wordSize_tendsto k).eventually_ge_atTop 1]
    with L hpositive herror hm1
  intro Q b nc hnc hb E hE χ a z hχ hz B hB S X R M₀ M₁ hX hR hM₀ hS hgood
    hcount hNorm hUnion hM hmin hwindow hsmall
  let m := wordSize k L
  let α := Real.exp (-Cw*(m : ℝ))*δ^nc
  have hp := hpositive nc hnc ((S.card : ℝ)/Real.sqrt X) hcount
  have he := herror Q b nc hnc hb E hE X M₀ hX hNorm hUnion hM
  have ha := hamp E hE χ a z B S α X R M₀ M₁ hχ hz hB (by dsimp [α]; positivity)
    hX hR hM₀ hS hgood hmin hwindow hsmall
  have hid : cψ*((S.card : ℝ)/Real.sqrt X)*α^2 = cψ*(S.card : ℝ)*α^2/Real.sqrt X := by ring
  change Real.exp (-positiveRate Cw CI*(m : ℝ)) ≤
    cψ*((S.card : ℝ)/Real.sqrt X)*α^2 at hp
  rw [hid] at hp
  have hhalf : (1/2)*Real.exp (-positiveRate Cw CI*(m : ℝ)) ≤
      ‖initialCharacterAmplitude (characterDoubleShell E) (characterDoubleShell_positive E hE)
        (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase z)
        (characterDoubleMask B) X‖ := by linarith
  apply le_trans _ hhalf
  have hsmallExp : Real.exp (-(m : ℝ)) ≤ (1/2 : ℝ) := by
    have htwo : (2 : ℝ) ≤ Real.exp (m : ℝ) := by
      have hh := Real.add_one_le_exp (m : ℝ)
      change 1 ≤ (m : ℝ) at hm1
      linarith
    simpa only [one_div, ← Real.exp_neg] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo
  have heq : Real.exp (-amplitudeRate Cw CI*(m : ℝ)) =
      Real.exp (-(m : ℝ))*Real.exp (-positiveRate Cw CI*(m : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    unfold amplitudeRate
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hsmallExp (Real.exp_pos _).le

end Ostmann.Characters.InitialCharacterScale

end

end OAI
