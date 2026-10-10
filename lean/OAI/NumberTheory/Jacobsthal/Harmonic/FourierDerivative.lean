import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Estimates.SeparatedSampling

namespace OAI

namespace Erdos970

section

open MeasureTheory Set Complex
open scoped BigOperators ComplexConjugate

namespace AdditiveLargeSieve

noncomputable def monomial (n : ℤ) (x : ℝ) : ℂ := fourier n (x : AddCircle (1 : ℝ))
noncomputable def polynomial (s : Finset ℤ) (b : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ s, b n * monomial n x

theorem monomial_continuous (n : ℤ) : Continuous (monomial n) :=
  (fourier n).continuous.comp (AddCircle.continuous_mk' 1)

theorem polynomial_continuous (s : Finset ℤ) (b : ℤ → ℂ) : Continuous (polynomial s b) := by
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul (monomial_continuous n)

theorem unit_monomial_integral (n : ℤ) (a : ℝ) :
    (∫ x in a..a + 1, monomial n x) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  rw [fourierCoeff_eq_intervalIntegral _ _ a] at h
  simpa [monomial, Pi.single_apply, eq_comm] using h

theorem monomial_conj_mul (n m : ℤ) (x : ℝ) :
    conj (monomial n x) * monomial m x = monomial (m - n) x := by
  simp only [monomial, ← fourier_neg, ← fourier_add]
  congr 2
  omega

theorem polynomial_square_expansion (s : Finset ℤ) (b : ℤ → ℂ) (x : ℝ) :
    conj (polynomial s b x) * polynomial s b x =
      ∑ n ∈ s, ∑ m ∈ s, (conj (b n) * b m) * monomial (m - n) x := by
  simp only [polynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  rw [← monomial_conj_mul]
  ring

theorem polynomial_energy (s : Finset ℤ) (b : ℤ → ℂ) (a : ℝ) :
    (∫ x in a..a + 1, ‖polynomial s b x‖ ^ 2) = ∑ n ∈ s, ‖b n‖ ^ 2 := by
  have h : (∫ x in a..a + 1, conj (polynomial s b x) * polynomial s b x) =
      ∑ n ∈ s, conj (b n) * b n := by
    simp_rw [polynomial_square_expansion]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [intervalIntegral.integral_finsetSum]
      · simp_rw [intervalIntegral.integral_const_mul, unit_monomial_integral]
        simp [sub_eq_zero, hn]
      · intro m _
        exact (continuous_const.mul (monomial_continuous _)).intervalIntegrable _ _
    · intro n _
      apply Continuous.intervalIntegrable
      exact continuous_finsetSum _ fun m _ => continuous_const.mul (monomial_continuous _)
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simpa only [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_sum] using h

theorem polynomial_energy_two (s : Finset ℤ) (b : ℤ → ℂ) :
    (∫ x in (0 : ℝ)..2, ‖polynomial s b x‖ ^ 2) = 2 * ∑ n ∈ s, ‖b n‖ ^ 2 := by
  have hc := (polynomial_continuous s b).norm.pow 2
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 2)
  simp only [Pi.pow_apply] at hsum
  have h0 := polynomial_energy s b 0
  have h1 := polynomial_energy s b 1
  norm_num only [zero_add, one_add_one_eq_two] at h0 h1
  linarith

end AdditiveLargeSieve

end

section

open MeasureTheory Set Complex
open scoped BigOperators ComplexConjugate RealInnerProductSpace

namespace AdditiveLargeSieve

noncomputable def derivativeCoefficients (b : ℤ → ℂ) (n : ℤ) : ℂ :=
  (2 * Real.pi * I * n) * b n

theorem polynomial_hasDerivAt (s : Finset ℤ) (b : ℤ → ℂ) (x : ℝ) :
    HasDerivAt (polynomial s b) (polynomial s (derivativeCoefficients b) x) x := by
  have h := HasDerivAt.fun_sum (u := s) fun n _ =>
    (hasDerivAt_fourier (1 : ℝ) n x).const_mul (b n)
  convert! h using 1
  simp only [polynomial, derivativeCoefficients, Complex.ofReal_one, div_one, monomial]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem derivative_coefficient_norm (b : ℤ → ℂ) (n : ℤ) :
    ‖derivativeCoefficients b n‖ = 2 * Real.pi * |(n : ℝ)| * ‖b n‖ := by
  simp [derivativeCoefficients, Complex.norm_intCast]

theorem derivative_energy_le (s : Finset ℤ) (b : ℤ → ℂ) {R : ℝ} (hR : 0 < R)
    (hfreq : ∀ n ∈ s, |(n : ℝ)| ≤ R) :
    (∫ x in (0 : ℝ)..2, ‖polynomial s (derivativeCoefficients b) x‖ ^ 2) ≤
      2 * (2 * Real.pi * R) ^ 2 * ∑ n ∈ s, ‖b n‖ ^ 2 := by
  rw [polynomial_energy_two, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [derivative_coefficient_norm]
  have h : 2 * Real.pi * |(n : ℝ)| * ‖b n‖ ≤ 2 * Real.pi * R * ‖b n‖ := by
    gcongr
    exact hfreq n hn
  have hnonneg : 0 ≤ 2 * Real.pi * |(n : ℝ)| * ‖b n‖ := by positivity
  have hnonneg' : 0 ≤ 2 * Real.pi * R * ‖b n‖ := by positivity
  nlinarith [sq_le_sq₀ hnonneg hnonneg' |>.2 h]

theorem norm_square_derivative_bound (z w : ℂ) {R : ℝ} (hR : 0 < R) :
    |2 * inner ℝ z w| ≤ R * ‖z‖ ^ 2 + R⁻¹ * ‖w‖ ^ 2 := by
  calc
    |2 * inner ℝ z w| = 2 * |inner ℝ z w| := by rw [abs_mul]; norm_num
    _ ≤ 2 * (‖z‖ * ‖w‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm z w) (by norm_num)
    _ ≤ _ := by
      apply (mul_le_mul_iff_right₀ hR).mp
      field_simp
      nlinarith [sq_nonneg (R * ‖z‖ - ‖w‖)]

theorem separated_polynomial_bound {ι : Type*} (samples : Finset ι) (t : ι → ℝ)
    (s : Finset ℤ) (b : ℤ → ℂ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hpoints : ∀ i ∈ samples, t i ∈ Icc (0 : ℝ) 1)
    (hsep : ∀ i ∈ samples, ∀ j ∈ samples, i ≠ j → δ ≤ |t i - t j|)
    (hfreq : ∀ n ∈ s, |(n : ℝ)| ≤ R) :
    (∑ i ∈ samples, ‖polynomial s b (t i)‖ ^ 2) ≤
      (4 + 8 * Real.pi ^ 2) * (R + δ⁻¹) * ∑ n ∈ s, ‖b n‖ ^ 2 := by
  let F := polynomial s b
  let D := polynomial s (derivativeCoefficients b)
  have hF : Continuous F := polynomial_continuous s b
  have hD : Continuous D := polynomial_continuous s _
  have hsample := separated_sampling samples t hδ (by norm_num : (0 : ℝ) ≤ 2)
    (fun i hi => ⟨(hpoints i hi).1, by linarith [(hpoints i hi).2]⟩) hsep
    (hF.norm.pow 2) ((continuous_const.mul (hF.inner hD)) : Continuous (fun x => 2 * inner ℝ (F x) (D x)))
    (fun x => (polynomial_hasDerivAt s b x).norm_sq) (fun x => sq_nonneg ‖F x‖)
  have hderiv : (∫ x in (0 : ℝ)..2, |2 * inner ℝ (F x) (D x)|) ≤
      R * (∫ x in (0 : ℝ)..2, ‖F x‖ ^ 2) + R⁻¹ * (∫ x in (0 : ℝ)..2, ‖D x‖ ^ 2) := by
    have h := intervalIntegral.integral_mono (μ := volume) (by norm_num : (0 : ℝ) ≤ 2)
      ((continuous_const.mul (hF.inner hD)).abs.intervalIntegrable 0 2)
      (((continuous_const.mul (hF.norm.pow 2)).add
        (continuous_const.mul (hD.norm.pow 2))).intervalIntegrable 0 2)
      (fun x => norm_square_derivative_bound (F x) (D x) hR)
    have hiF : IntervalIntegrable (fun x => R * ‖F x‖ ^ 2) volume 0 2 :=
      (continuous_const.mul (hF.norm.pow 2)).intervalIntegrable _ _
    have hiD : IntervalIntegrable (fun x => R⁻¹ * ‖D x‖ ^ 2) volume 0 2 :=
      (continuous_const.mul (hD.norm.pow 2)).intervalIntegrable _ _
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at h
    rw [intervalIntegral.integral_add hiF hiD,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    exact h
  have hE : (∫ x in (0 : ℝ)..2, ‖F x‖ ^ 2) = 2 * ∑ n ∈ s, ‖b n‖ ^ 2 := polynomial_energy_two s b
  have hDE := derivative_energy_le s b hR hfreq
  have hEpos : 0 ≤ ∑ n ∈ s, ‖b n‖ ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  simp only [Pi.pow_apply, Pi.mul_apply] at hsample
  have hfinal := hsample.trans (add_le_add le_rfl hderiv)
  rw [hE] at hfinal
  have hbound := mul_le_mul_of_nonneg_left hDE (inv_nonneg.mpr hR.le)
  have halgebra : δ⁻¹ * (2 * ∑ n ∈ s, ‖b n‖ ^ 2) +
      (R * (2 * ∑ n ∈ s, ‖b n‖ ^ 2) + R⁻¹ *
        (2 * (2 * Real.pi * R) ^ 2 * ∑ n ∈ s, ‖b n‖ ^ 2)) =
      (2 * δ⁻¹ + (2 + 8 * Real.pi ^ 2) * R) * ∑ n ∈ s, ‖b n‖ ^ 2 := by
    field_simp
    ring
  have hc : 2 * δ⁻¹ + (2 + 8 * Real.pi ^ 2) * R ≤
      (4 + 8 * Real.pi ^ 2) * (R + δ⁻¹) := by
    have := mul_nonneg (sq_nonneg Real.pi) (inv_nonneg.mpr hδ.le)
    have := inv_nonneg.mpr hδ.le
    nlinarith
  have hjoin : (∑ i ∈ samples, ‖F (t i)‖ ^ 2) ≤
      (2 * δ⁻¹ + (2 + 8 * Real.pi ^ 2) * R) * ∑ n ∈ s, ‖b n‖ ^ 2 := by
    rw [← halgebra]
    exact hfinal.trans (add_le_add le_rfl (add_le_add le_rfl hbound))
  exact hjoin.trans (mul_le_mul_of_nonneg_right hc hEpos)

end AdditiveLargeSieve

end

end Erdos970

end OAI
