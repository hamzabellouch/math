import OAI.MeasureTheory.Falconer.Slicing.GaussianSliceMoment

namespace OAI

/-! # Finite-scale second moments of Gaussian direction slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_pair_kernel_factor (h : ℕ) (r a : ℝ) :
    (2*gaussianPairBandConstant*r^2/(a+r))^h =
      (2*gaussianPairBandConstant*r^2)^h*(1/(a+r))^(h:ℝ) := by
  rw [Real.rpow_natCast,div_pow,one_div,inv_pow,div_eq_mul_inv]

theorem gaussian_direction_second_moment_frostman
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (k : ℕ)
    (hmass : ν univ ≤ 1)
    (hball : ∀ w : Sphere d, ∀ n : ℕ, n ≤ k →
      ν (ball w (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d)) :
    (∫⁻ A : Fin h → Space d,
      (ν (gaussianDirectionBand A (1/(2:ℝ)^k)))^2 ∂gaussianRows d h) ≤
      ENNReal.ofReal ((2*gaussianPairBandConstant*(1/(2:ℝ)^k)^2)^h)*
        (ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1) := by
  let r : ℝ := 1/(2:ℝ)^k
  let C : ℝ≥0∞ := ENNReal.ofReal ((2*gaussianPairBandConstant*r^2)^h)
  let B : ℝ≥0∞ := ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1
  have hp (w : Sphere d) :
      (∫⁻ v, ENNReal.ofReal ((1/(dist w v+r))^(h:ℝ)) ∂ν) ≤ B :=
    regularized_potential_global ν w hK (Nat.cast_nonneg _) hq k hmass (hball w)
  apply (gaussian_direction_band_second_moment_bound ν (by positivity) hchart).trans
  calc
    _ = C * ∫⁻ z : Sphere d × Sphere d,
        ENNReal.ofReal ((1/(dist z.1 z.2+r))^(h:ℝ)) ∂ν.prod ν := by
      change (∫⁻ z : Sphere d × Sphere d,
        ENNReal.ofReal ((2*gaussianPairBandConstant*r^2/(dist z.1 z.2+r))^h) ∂ν.prod ν) = _
      rw [← lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      rw [gaussian_pair_kernel_factor,ENNReal.ofReal_mul
        (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          gaussianPairBandConstant_pos.le) (sq_nonneg r)) h)]
    _ = C * ∫⁻ w, ∫⁻ v, ENNReal.ofReal ((1/(dist w v+r))^(h:ℝ)) ∂ν ∂ν := by
      rw [lintegral_prod _ (by fun_prop)]
    _ ≤ C * ∫⁻ _ : Sphere d, B ∂ν := mul_le_mul_right (lintegral_mono hp) C
    _ = C*(B*ν univ) := by rw [lintegral_const]
    _ ≤ C*(B*1) := by gcongr
    _ = _ := by simp [C,B,r]

end Falconer

end OAI
