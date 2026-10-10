import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedRealZeros
import OAI.NumberTheory.Ostmann.ZeroDensity.DirichletLogDerivativeBound

namespace OAI

/-! # Deriving signed prime-mass bounds from the published zero expansion -/

namespace Ostmann

open scoped BigOperators

theorem realCharacterZeroExpansion_anchor {χ : PrimitiveRealCharacter} {C : ℝ}
    (Z : RealCharacterZeroExpansion χ C) (s₀ L A : ℝ)
    (hs : 1 < s₀) (hs2 : s₀ ≤ 2) (hlog : Real.log χ.modulus ≤ L)
    (hderiv : χ.logDerivative s₀ ≤ L + A) (herror : A + C ≤ L / 2) :
    (∑' i, realZeroKernel (s₀ - (Z.zeros i).re) (Z.zeros i).im) ≤ 2 * L := by
  have hh := (abs_le.mp (Z.hadamard s₀ hs hs2)).2
  linarith

/-- The bounded Euler prime-power error has already been proved. Only the
Hadamard expansion remains an input to this implication. -/
theorem exists_signed_prime_lower_of_zero_sum :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (χ : PrimitiveRealCharacter) (C : ℝ)
      (Z : RealCharacterZeroExpansion χ C) (s B : ℝ), 1 < s → s ≤ 2 →
      (∑' i, realZeroKernel (s - (Z.zeros i).re) (Z.zeros i).im) ≤ B →
      -B - C - A ≤ ∑' n, realPrimeTerm χ.character s n := by
  obtain ⟨A, hA, heuler⟩ := exists_realPrimeSeries_error
  refine ⟨A, hA, ?_⟩
  intro χ C Z s B hs hs2 hzeros
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have he := (heuler χ.modulus χ.character s hs).2
  change |(∑' n, realPrimeTerm χ.character s n) + χ.logDerivative s| ≤ A at he
  have hh := (abs_le.mp (Z.hadamard s hs hs2)).1
  have hlog : 0 ≤ Real.log (χ.modulus : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast χ.positive
  have he' := (abs_le.mp he).1
  linarith

/-- Actual real exceptions in a finite zero family cost at most one Siegel
term when the region has at most one exceptional zero. -/
theorem exceptional_zero_sum_bound (hSiegel : PublishedSiegelBound)
    (ε : ℝ) (hε : 0 < ε) : ∃ K : ℝ, 0 < K ∧
    ∀ (χ : PrimitiveRealCharacter) (C : ℝ) (Z : RealCharacterZeroExpansion χ C)
      (E : Finset ℕ) (s : ℝ), E.card ≤ 1 → 1 < s →
      (∀ i ∈ E, (Z.zeros i).im = 0) →
      (∑ i ∈ E, (s - (Z.zeros i).re)⁻¹) ≤ K * (χ.modulus : ℝ) ^ ε := by
  obtain ⟨K, hK, hbound⟩ := hSiegel ε hε
  refine ⟨K, hK, ?_⟩
  intro χ C Z E s hE hs hreal
  have hf (i : ℕ) (hi : i ∈ E) : (s - (Z.zeros i).re)⁻¹ ≤ K * (χ.modulus : ℝ) ^ ε := by
    have hβ := (Z.in_strip i).2
    have he := hbound (Z.realZero i (hreal i hi))
    change (1 - (Z.zeros i).re)⁻¹ ≤ K * (χ.modulus : ℝ) ^ ε at he
    have hinv : (s - (Z.zeros i).re)⁻¹ ≤ (1 - (Z.zeros i).re)⁻¹ :=
      inv_anti₀ (by linarith) (by linarith)
    exact hinv.trans he
  calc
    _ ≤ (E.card : ℝ) * (K * (χ.modulus : ℝ) ^ ε) := by
      simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul E _ _ hf
    _ ≤ K * (χ.modulus : ℝ) ^ ε := by
      have hER : (E.card : ℝ) ≤ 1 := by exact_mod_cast hE
      have hnn : 0 ≤ K * (χ.modulus : ℝ) ^ ε := by positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hER hnn

end Ostmann

end OAI
