import OAI.NumberTheory.Ostmann.ZeroDensity.DensityCharacterFamily
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDiscreteHybrid

namespace OAI

/-! # The hybrid sieve for the actual primitive-character index type -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem density_primitive_hybrid_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ.character t‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := hybrid_multiplicative_large_sieve
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T hT a F hF
  rw [densityCharacterFamily_sum F Q hF (fun q χ => ∫ t in Icc (-T) T,
    ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ t‖ ^ 2)]
  exact hb N Q hQ T hT a (densityCharacterFamily F)
    (fun q _ χ hχ => densityCharacterFamily_primitive F q χ hχ)

 theorem density_primitive_discrete_hybrid :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∑ i ∈ R, ‖densityCharacterPolynomial (Finset.Icc 1 N) a (c i).character (t i)‖ ^ 2) ≤
        C * ((N : ℝ) + (Q : ℝ) ^ 2 * (T + 1)) *
          (2 + 64 * (Real.log (N + 1 : ℕ)) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := density_primitive_hybrid_mean
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T hT a ι R c t hc ht hsep
  let F := R.image c
  have hF : ∀ χ ∈ F, χ.modulus ≤ Q := by
    intro χ hχ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hχ
    exact hc i hi
  have hpoint (χ : PrimitiveComplexCharacter) :
      (∑ i ∈ R.filter (fun i => c i = χ),
        ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ.character (t i)‖ ^ 2) ≤
      2 * (∫ u in Icc (-(T + 1)) (T + 1),
        ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ.character u‖ ^ 2) +
        ∫ u in Icc (-(T + 1)) (T + 1),
          ‖densityCharacterPolynomial (Finset.Icc 1 N) (densityDerivativeCoeff a) χ.character u‖ ^ 2 := by
    have hder (n : ℕ) : densityDerivativeCoeff (fun m => a m * χ.character (m : ZMod χ.modulus)) n =
        densityDerivativeCoeff a n * χ.character (n : ZMod χ.modulus) := by
      unfold densityDerivativeCoeff
      ring
    have h := density_separated_samples (R.filter (fun i => c i = χ)) t T
      (fun i hi => ht i (Finset.mem_filter.mp hi).1)
      (fun i hi j hj hij => hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
        ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) hij)
      (fun u => ∑ n ∈ Finset.Icc 1 N, (a n * χ.character (n : ZMod χ.modulus)) *
        realAdditivePhase (-(Real.log n * u)))
      (fun u => ∑ n ∈ Finset.Icc 1 N,
        densityDerivativeCoeff (fun m => a m * χ.character (m : ZMod χ.modulus)) n *
          realAdditivePhase (-(Real.log n * u)))
      (density_polynomial_hasDerivAt _ _) (density_polynomial_continuous _ _)
    simpa only [hder, densityCharacterPolynomial, show -T - 1 = -(T + 1) by ring] using h
  have he : (∑ i ∈ R, ‖densityCharacterPolynomial (Finset.Icc 1 N) a (c i).character (t i)‖ ^ 2) =
      ∑ χ ∈ F, ∑ i ∈ R.filter (fun i => c i = χ),
        ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ.character (t i)‖ ^ 2 := by
    have hmap : ∀ i ∈ R, c i ∈ F := fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    apply Finset.sum_congr rfl
    intro χ _
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [he]
  have hs := Finset.sum_le_sum (s := F) (fun χ _ => hpoint χ)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have ha := hb N Q hQ (T + 1) (by linarith) a F hF
  have hd := hb N Q hQ (T + 1) (by linarith) (densityDerivativeCoeff a) F hF
  have hd' := hd.trans (mul_le_mul_of_nonneg_left (density_derivative_coefficient_bound N a) (by positivity))
  apply hs.trans
  have h := add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 2)) hd'
  convert h using 1
  ring

end Ostmann

end OAI
