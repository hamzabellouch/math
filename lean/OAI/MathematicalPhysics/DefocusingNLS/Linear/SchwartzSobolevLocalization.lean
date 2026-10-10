import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzLocalizationKernel

namespace OAI

/-! # Weighted finite Fourier localization

This proves the weighted mixed Fourier bound in the verification of (lin:J-bound).
The kernel is a genuine Schwartz function; its positive Bessel-weighted modulus
is used only inside the Schur estimate. The later Fourier change of variables
must still carry the chosen Fourier normalization.
-/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

private theorem localization_bessel_product (s : ℝ) (hs : 0 ≤ s)
    (x y : EuclideanSpace ℝ (Fin 12)) :
    (1 + ‖x‖ ^ 2) ^ (s / 2) ≤ 2 ^ (s / 2) *
      (1 + ‖y‖ ^ 2) ^ (s / 2) * (1 + ‖x - y‖ ^ 2) ^ (s / 2) := by
  have hn : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    have hid : y + (x - y) = x := by abel
    simpa only [hid] using norm_add_le y (x - y)
  have hbase : 1 + ‖x‖ ^ 2 ≤ 2 * (1 + ‖y‖ ^ 2) * (1 + ‖x - y‖ ^ 2) := by
    nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x - y),
      sq_nonneg (‖y‖ - ‖x - y‖), mul_nonneg (sq_nonneg ‖y‖) (sq_nonneg ‖x - y‖)]
  calc
    _ ≤ (2 * (1 + ‖y‖ ^ 2) * (1 + ‖x - y‖ ^ 2)) ^ (s / 2) :=
      Real.rpow_le_rpow (by positivity) hbase (by positivity)
    _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]

private theorem localization_bessel_square (s : ℝ) (x : EuclideanSpace ℝ (Fin 12)) :
    ((1 + ‖x‖ ^ 2) ^ (s / 2)) ^ 2 = (1 + ‖x‖ ^ 2) ^ s := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- Uniform finite-sum estimate for the Sobolev-weighted localization kernel. -/
theorem exists_schwartz_sobolev_localization_bound (s : ℝ) (hs : 0 ≤ s)
    (K : 𝓢(EuclideanSpace ℝ (Fin 12), ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset frequencyLattice) (v : frequencyLattice → ℂ),
      Integrable (fun x => (1 + ‖x‖ ^ 2) ^ s * ‖∑ n ∈ S, v n * K (x - n)‖ ^ 2) ∧
        (∫ x, (1 + ‖x‖ ^ 2) ^ s * ‖∑ n ∈ S, v n * K (x - n)‖ ^ 2) ≤
          C * ∑ n ∈ S, (1 + ‖n‖ ^ 2) ^ s * ‖v n‖ ^ 2 := by
  classical
  let W := weightedSchwartzKernel s K
  let P : EuclideanSpace ℝ (Fin 12) → ℂ := fun x => (‖W x‖ : ℂ)
  obtain ⟨C₀, hC₀, hperiod⟩ := exists_schwartz_periodization_bound W
  have hP : Integrable P := W.integrable.norm.ofReal
  have hPn (x : EuclideanSpace ℝ (Fin 12)) : ‖P x‖ = ‖W x‖ := by
    simp only [P, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  let C₁ := C₀ * ∫ x, ‖W x‖
  have hC₁ : 0 ≤ C₁ := mul_nonneg hC₀ (integral_nonneg (fun _ => norm_nonneg _))
  let c : ℝ := 2 ^ (s / 2)
  refine ⟨c ^ 2 * C₁, mul_nonneg (sq_nonneg _) hC₁, ?_⟩
  intro S v
  let A : frequencyLattice → ℂ := fun n => ((1 + ‖n‖ ^ 2) ^ (s / 2) * ‖v n‖ : ℝ)
  let F : EuclideanSpace ℝ (Fin 12) → ℝ := fun x =>
    ∑ n ∈ S, (1 + ‖n‖ ^ 2) ^ (s / 2) * ‖v n‖ * ‖W (x - n)‖
  have hF_nonneg (x) : 0 ≤ F x := by
    apply Finset.sum_nonneg
    intro n _
    positivity
  have hF_eq (x) : ‖∑ n ∈ S, A n * P (x - n)‖ = F x := by
    have heq : (∑ n ∈ S, A n * P (x - n)) = (F x : ℂ) := by
      simp only [A, P, F, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF_nonneg x)]
  obtain ⟨hFI, hFB⟩ := mixedFourier_integral_bound S A P hP C₀ hC₀ (by
    intro x
    simpa only [hPn] using hperiod S x)
  simp only [hF_eq] at hFI hFB
  have hpoint (x : EuclideanSpace ℝ (Fin 12)) :
      (1 + ‖x‖ ^ 2) ^ (s / 2) * ‖∑ n ∈ S, v n * K (x - n)‖ ≤ c * F x := by
    calc
      _ ≤ (1 + ‖x‖ ^ 2) ^ (s / 2) * ∑ n ∈ S, ‖v n‖ * ‖K (x - n)‖ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [norm_mul] using norm_sum_le S (fun n => v n * K (x - n))
      _ = ∑ n ∈ S, (1 + ‖x‖ ^ 2) ^ (s / 2) * (‖v n‖ * ‖K (x - n)‖) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ n ∈ S, c * ((1 + ‖n‖ ^ 2) ^ (s / 2) * ‖v n‖ * ‖W (x - n)‖) := by
        apply Finset.sum_le_sum
        intro n _
        calc
          _ ≤ (2 ^ (s / 2) * (1 + ‖n‖ ^ 2) ^ (s / 2) *
              (1 + ‖x - n‖ ^ 2) ^ (s / 2)) * (‖v n‖ * ‖K (x - n)‖) :=
            mul_le_mul_of_nonneg_right (localization_bessel_product s hs x n) (by positivity)
          _ = _ := by
            rw [show ‖W (x - n)‖ = _ from weightedSchwartzKernel_norm s K (x - n)]
            dsimp [c]
            ring
      _ = _ := by rw [← Finset.mul_sum]
  have hsquare (x : EuclideanSpace ℝ (Fin 12)) :
      (1 + ‖x‖ ^ 2) ^ s * ‖∑ n ∈ S, v n * K (x - n)‖ ^ 2 ≤ c ^ 2 * F x ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤
      (1 + ‖x‖ ^ 2) ^ (s / 2) * ‖∑ n ∈ S, v n * K (x - n)‖) (hpoint x) 2
    simpa only [mul_pow, localization_bessel_square] using h
  have hcont : Continuous (fun x =>
      (1 + ‖x‖ ^ 2) ^ s * ‖∑ n ∈ S, v n * K (x - n)‖ ^ 2) := by
    have hK : Continuous K := K.continuous
    fun_prop
  have hI : Integrable (fun x =>
      (1 + ‖x‖ ^ 2) ^ s * ‖∑ n ∈ S, v n * K (x - n)‖ ^ 2) := by
    apply (hFI.const_mul (c ^ 2)).mono' hcont.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hsquare x
  refine ⟨hI, (integral_mono hI (hFI.const_mul (c ^ 2)) hsquare).trans ?_⟩
  rw [integral_const_mul]
  have hAn (n : frequencyLattice) : ‖A n‖ ^ 2 = (1 + ‖n‖ ^ 2) ^ s * ‖v n‖ ^ 2 := by
    simp only [A, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), mul_pow]
    have hn := localization_bessel_square s (n : EuclideanSpace ℝ (Fin 12))
    change ((1 + ‖n‖ ^ 2) ^ (s / 2)) ^ 2 = (1 + ‖n‖ ^ 2) ^ s at hn
    rw [hn]
  simp only [hPn, hAn] at hFB
  exact (mul_le_mul_of_nonneg_left hFB (sq_nonneg c)).trans_eq (by dsimp [C₁]; ring)

end DefocusingNLS

end OAI
