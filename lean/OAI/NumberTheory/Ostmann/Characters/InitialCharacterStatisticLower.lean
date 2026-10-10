import OAI.NumberTheory.Ostmann.Characters.CharacterRepeatedTuplesBound
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticExpansion
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticProperties

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Characters
open Construction Preliminaries

def initialCharacterRepeatedError {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q))
    (X M₀ : ℝ) : ℝ :=
  (Real.sqrt X*‖𝓕 SchwartzCutoff.psi 0‖*(∏ i, (primeShellMass (E i))⁻¹)^2/Real.sqrt M₀)*
    (((b+b : ℕ) : ℝ)^(b+b)*Real.exp (primeShellMass (Finset.univ.biUnion E)))

theorem initialCharacterAmplitude_lower {Q b : ℕ}
    (E : Fin b → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (hχ : ∀ i, ∀ p ∈ E i, χ i p.val ≠ 1)
    (hz : ∀ i, ∀ p ∈ E i, ‖z i p.val‖ ≤ 1)
    (B : (Fin b → PrimeUpTo Q) → ℝ) (hB : ∀ w, 0 ≤ B w ∧ B w ≤ 1)
    {X R M₀ M₁ : ℝ} (hX : 0 < X) (hR : 0 < R) (hM₀ : 0 < M₀)
    (hmin : ∀ i, ∀ p ∈ E i, R ≤ (p.val : ℝ))
    (hwindow : ∀ w : Fin (b+b) → PrimeUpTo Q,
      (∀ i, w i ∈ characterDoubleShell E i) → characterDoubleMask B w ≠ 0 →
      M₀ ≤ (characterTupleProduct w : ℝ) ∧ (characterTupleProduct w : ℝ) ≤ M₁)
    (hsmall : M₁ < 4*X*R) :
    initialCharacterStatistic X (initialCharacterMean E hE χ a z B)/Real.sqrt X -
      initialCharacterRepeatedError E X M₀ ≤
      ‖initialCharacterAmplitude (characterDoubleShell E) (characterDoubleShell_positive E hE)
        (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase z)
        (characterDoubleMask B) X‖ := by
  have hdχ := characterDoubleChar_nonprincipal E χ hχ
  have herr := characterRepeatedContribution_bound (characterDoubleShell E)
    (characterDoubleShell_positive E hE) (characterDoubleChar χ) (characterDoubleCenter a)
    (characterDoublePhase z) hdχ (characterDoublePhase_bound E z hz)
    (characterDoubleMask B) (characterDoubleMask_bounds B hB) hX hR hM₀
    (characterDoubleShell_min E hmin) hwindow hsmall
  rw [characterDoubleShell_normalization, characterDoubleShell_union] at herr
  change ‖characterRepeatedContribution (characterDoubleShell E) (characterDoubleShell_positive E hE)
    (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase z)
    (characterDoubleMask B) X‖ ≤ initialCharacterRepeatedError E X M₀ at herr
  have he := initialCharacterStatistic_eq_distinct_add_repeated E hE χ a z B hX
  rw [characterDistinctContribution_eq_amplitude _ _ _ _ _ hdχ _ hX] at he
  have hI : 0 ≤ initialCharacterStatistic X (initialCharacterMean E hE χ a z B) :=
    tsum_nonneg (fun n => mul_nonneg (SchwartzCutoff.psi_nonneg _) (sq_nonneg _))
  have hn := norm_add_le (initialCharacterAmplitude (characterDoubleShell E)
    (characterDoubleShell_positive E hE) (characterDoubleChar χ) (characterDoubleCenter a)
    (characterDoublePhase z) (characterDoubleMask B) X)
    (characterRepeatedContribution (characterDoubleShell E) (characterDoubleShell_positive E hE)
      (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase z)
      (characterDoubleMask B) X)
  rw [← he, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hI, abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  linarith

theorem exists_initialCharacterAmplitude_constant : ∃ cψ : ℝ, 0 < cψ ∧
    ∀ {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
      (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
      (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
      (B : (Fin b → PrimeUpTo Q) → ℝ) (H : Finset ℤ) (α X R M₀ M₁ : ℝ),
      (∀ i, ∀ p ∈ E i, χ i p.val ≠ 1) → (∀ i, ∀ p ∈ E i, ‖z i p.val‖ ≤ 1) →
      (∀ w, 0 ≤ B w ∧ B w ≤ 1) → 0 ≤ α → 0 < X → 0 < R → 0 < M₀ →
      (∀ n ∈ H, |(n : ℝ)/X| ≤ 1) →
      (∀ n ∈ H, α ≤ ‖initialCharacterMean E hE χ a z B n‖) →
      (∀ i, ∀ p ∈ E i, R ≤ (p.val : ℝ)) →
      (∀ w : Fin (b+b) → PrimeUpTo Q,
        (∀ i, w i ∈ characterDoubleShell E i) → characterDoubleMask B w ≠ 0 →
        M₀ ≤ (characterTupleProduct w : ℝ) ∧ (characterTupleProduct w : ℝ) ≤ M₁) →
      M₁ < 4*X*R →
      cψ*(H.card : ℝ)*α^2/Real.sqrt X-initialCharacterRepeatedError E X M₀ ≤
      ‖initialCharacterAmplitude (characterDoubleShell E) (characterDoubleShell_positive E hE)
        (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase z)
        (characterDoubleMask B) X‖ := by
  obtain ⟨cψ,hc,hstat⟩ := exists_initialCharacterStatistic_constant
  refine ⟨cψ,hc,?_⟩
  intro Q b E hE χ a z B H α X R M₀ M₁ hχ hz hB hα hX hR hM₀ hH hgood hmin hwin hsmall
  have hpos := hstat E hE χ a z B H X α hz
    (fun w => by rw [abs_of_nonneg (hB w).1]; exact (hB w).2) hX hα hH hgood
  have hn := initialCharacterAmplitude_lower E hE χ a z hχ hz B hB hX hR hM₀ hmin hwin hsmall
  have hd := div_le_div_of_nonneg_right hpos (Real.sqrt_nonneg X)
  linarith

end Ostmann.Characters

end

end OAI
