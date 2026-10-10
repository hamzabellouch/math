import OAI.NumberTheory.Ostmann.ZeroDensity.DensityPolynomialDerivative

namespace OAI

/-! # The hybrid large sieve at separated ordinates -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem discrete_hybrid_multiplicative_large_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ F : (q : ℕ) → Finset (DirichletCharacter ℂ q),
      (∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) →
      ∀ (ι : Type) (R : (q : ℕ) → DirichletCharacter ℂ q → Finset ι)
        (t : (q : ℕ) → DirichletCharacter ℂ q → ι → ℝ),
      (∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, ∀ i ∈ R q χ, |t q χ i| ≤ T) →
      (∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, ∀ i ∈ R q χ, ∀ j ∈ R q χ,
        i ≠ j → 1 ≤ |t q χ i - t q χ j|) →
      (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q, ∑ i ∈ R q χ,
        ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q) *
          realAdditivePhase (-(Real.log n * t q χ i))‖ ^ 2) ≤
        C * ((N : ℝ) + (Q : ℝ) ^ 2 * (T + 1)) *
          (2 + 64 * (Real.log (N + 1 : ℕ)) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hmean⟩ := hybrid_multiplicative_large_sieve
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T hT a F hF ι R t ht hsep
  have hT1 : 1 ≤ T + 1 := by linarith
  have hder (q : ℕ) (χ : DirichletCharacter ℂ q) (n : ℕ) :
      densityDerivativeCoeff (fun m => a m * χ (m : ZMod q)) n =
        densityDerivativeCoeff a n * χ (n : ZMod q) := by
    unfold densityDerivativeCoeff
    ring
  have hpoint (q : ℕ) (hq : q ∈ Finset.Icc 1 Q) (χ : DirichletCharacter ℂ q) (hχ : χ ∈ F q) :
      (∑ i ∈ R q χ, ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q) *
        realAdditivePhase (-(Real.log n * t q χ i))‖ ^ 2) ≤
      2 * (∫ u in Icc (-(T + 1)) (T + 1), ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * u))‖ ^ 2) +
        ∫ u in Icc (-(T + 1)) (T + 1), ‖∑ n ∈ Finset.Icc 1 N,
          densityDerivativeCoeff a n * χ (n : ZMod q) *
            realAdditivePhase (-(Real.log n * u))‖ ^ 2 := by
    have hp := density_separated_samples (R q χ) (t q χ) T (ht q hq χ hχ) (hsep q hq χ hχ)
      (fun u => ∑ n ∈ Finset.Icc 1 N, (a n * χ (n : ZMod q)) *
        realAdditivePhase (-(Real.log n * u)))
      (fun u => ∑ n ∈ Finset.Icc 1 N,
        densityDerivativeCoeff (fun m => a m * χ (m : ZMod q)) n *
          realAdditivePhase (-(Real.log n * u)))
      (density_polynomial_hasDerivAt _ _) (density_polynomial_continuous _ _)
    simpa only [hder, show -T - 1 = -(T + 1) by ring] using hp
  have hs := Finset.sum_le_sum (s := Finset.Icc 1 Q) (fun q hq =>
    Finset.sum_le_sum (s := F q) (fun χ hχ => hpoint q hq χ hχ))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have ha := hmean N Q hQ (T + 1) hT1 a F hF
  have hd := hmean N Q hQ (T + 1) hT1 (densityDerivativeCoeff a) F hF
  have hB : 0 ≤ C * ((N : ℝ) + (Q : ℝ) ^ 2 * (T + 1)) := by positivity
  have hd' := hd.trans (mul_le_mul_of_nonneg_left (density_derivative_coefficient_bound N a) hB)
  have hb := add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 2)) hd'
  apply hs.trans
  convert hb using 1
  ring

end Ostmann

end OAI
