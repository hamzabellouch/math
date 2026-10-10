import OAI.NumberTheory.Ostmann.ZeroDensity.DensityPrimitiveHybrid
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityAbscissaEnergy

namespace OAI

/-! # The hybrid sieve with different real parts at the sampled zeros -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem density_variable_abscissa_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ, 1 ≤ T → 0 ≤ σ → σ ≤ 1 →
      ∀ a : ℕ → ℂ, ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1) →
      (∑ i ∈ R, ‖densityCharacterPolynomial (Finset.Icc 1 N)
        (densityVerticalCoeff a (β i)) (c i).character (t i)‖ ^ 2) ≤
      C * ((N : ℝ) + (Q : ℝ) ^ 2 * (T + 1)) *
        (2 + 64 * (Real.log (N + 1 : ℕ)) ^ 2) * (2 + (Real.log (N + 1 : ℕ)) ^ 2) *
          ∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff a σ n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := density_primitive_discrete_hybrid
  refine ⟨2 * C, by positivity, ?_⟩
  intro N Q hQ T σ hT hσ0 hσ1 a ι R c t β hc ht hs hβ
  let E := ∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff a σ n‖ ^ 2
  let K := C * ((N : ℝ) + (Q : ℝ) ^ 2 * (T + 1)) * (2 + 64 * (Real.log (N + 1 : ℕ)) ^ 2)
  let F := fun x : ℝ => ∑ i ∈ R, ‖densityCharacterPolynomial (Finset.Icc 1 N)
    (densityVerticalCoeff a x) (c i).character (t i)‖ ^ 2
  let G := fun x : ℝ => ∑ i ∈ R, ‖densityCharacterPolynomial (Finset.Icc 1 N)
    (densityVerticalCoeff (densityAbscissaDerivativeCoeff a) x) (c i).character (t i)‖ ^ 2
  have hpos (n : ℕ) (hn : n ∈ Finset.Icc 1 N) : 0 < n := (Finset.mem_Icc.mp hn).1
  have hFc : Continuous F := continuous_finsetSum R (fun i _ =>
    ((density_abscissa_polynomial_continuous _ hpos a (c i).character (t i)).norm.pow 2))
  have hGc : Continuous G := continuous_finsetSum R (fun i _ =>
    ((density_abscissa_polynomial_continuous _ hpos (densityAbscissaDerivativeCoeff a) (c i).character (t i)).norm.pow 2))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hFb (x : ℝ) (hx : x ∈ Icc σ 2) : F x ≤ K * E := by
    have h := hb N Q hQ T hT (densityVerticalCoeff a x) R c t hc ht hs
    exact h.trans (mul_le_mul_of_nonneg_left (density_abscissa_energy_mono N a σ x hx.1) hK)
  have hGb (x : ℝ) (hx : x ∈ Icc σ 2) : G x ≤ K * ((Real.log (N + 1 : ℕ)) ^ 2 * E) := by
    have h := hb N Q hQ T hT (densityVerticalCoeff (densityAbscissaDerivativeCoeff a) x) R c t hc ht hs
    have he := (density_abscissa_energy_mono N (densityAbscissaDerivativeCoeff a) σ x hx.1).trans
      (density_abscissa_derivative_energy N a σ)
    exact h.trans (mul_le_mul_of_nonneg_left he hK)
  have hσ2 : σ ≤ 2 := by linarith
  have hIF : (∫ x in σ..2, F x) ≤ 2 * (K * E) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hσ2 (hFc.intervalIntegrable σ 2)
      intervalIntegrable_const hFb
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith : 2 - σ ≤ 2) (mul_nonneg hK hE))
  have hIG : (∫ x in σ..2, G x) ≤ 2 * (K * ((Real.log (N + 1 : ℕ)) ^ 2 * E)) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hσ2 (hGc.intervalIntegrable σ 2)
      intervalIntegrable_const hGb
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith : 2 - σ ≤ 2) (by positivity))
  have hsample := Finset.sum_le_sum (s := R) (fun i hi =>
    density_abscissa_polynomial_sample (Finset.Icc 1 N) hpos a (c i).character (t i) σ (β i)
      (hβ i hi).1 (hβ i hi).2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsample
  have heF : (∫ x in σ..2, F x) = ∑ i ∈ R, ∫ x in σ..2,
      ‖densityCharacterPolynomial (Finset.Icc 1 N) (densityVerticalCoeff a x) (c i).character (t i)‖ ^ 2 := by
    simpa only [F, Pi.pow_apply] using intervalIntegral.integral_finsetSum
      (μ := volume) (fun i (_hi : i ∈ R) =>
        ((density_abscissa_polynomial_continuous _ hpos a (c i).character (t i)).norm.pow 2).intervalIntegrable σ 2)
  have heG : (∫ x in σ..2, G x) = ∑ i ∈ R, ∫ x in σ..2,
      ‖densityCharacterPolynomial (Finset.Icc 1 N)
        (densityVerticalCoeff (densityAbscissaDerivativeCoeff a) x) (c i).character (t i)‖ ^ 2 := by
    simpa only [G, Pi.pow_apply] using intervalIntegral.integral_finsetSum
      (μ := volume) (fun i (_hi : i ∈ R) =>
        ((density_abscissa_polynomial_continuous _ hpos (densityAbscissaDerivativeCoeff a)
          (c i).character (t i)).norm.pow 2).intervalIntegrable σ 2)
  rw [← heF, ← heG] at hsample
  apply hsample.trans
  have h := add_le_add (mul_le_mul_of_nonneg_left hIF (by norm_num : (0 : ℝ) ≤ 2)) hIG
  convert h using 1
  dsimp [K, E]
  ring

end Ostmann

end OAI
