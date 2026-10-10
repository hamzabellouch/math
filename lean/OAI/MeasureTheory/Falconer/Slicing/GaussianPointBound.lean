import OAI.MeasureTheory.Falconer.Slicing.GaussianPointMoment
import OAI.MeasureTheory.Falconer.Slicing.GaussianSliceMass

namespace OAI

/-! # Point-slice second moments from the original finite-scale ball bounds -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_pair_kernel (x y : Space d) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((2*r)^h)*gaussianRows d h
      {A | ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r} ≤
      ENNReal.ofReal ((4*gaussianVectorBandConstant*r^2/(dist x y+r))^h) := by
  have hC := gaussianVectorBandConstant_pos
  calc
    _ ≤ ENNReal.ofReal ((2*r)^h)*
        ENNReal.ofReal ((gaussianVectorBandConstant*(2*r)/(‖x-y‖+2*r))^h) :=
      mul_le_mul_right (gaussianRows_vector_band (x-y) (by positivity)) _
    _ = ENNReal.ofReal ((4*gaussianVectorBandConstant*r^2/(dist x y+2*r))^h) := by
      rw [← ENNReal.ofReal_mul (by positivity),← mul_pow]
      congr 2
      rw [dist_eq_norm]
      field_simp
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply pow_le_pow_left₀ (by positivity)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith

theorem gaussian_point_band_second_moment_frostman
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (k : ℕ)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : Space d, ∀ n : ℕ, n ≤ k →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      (μ (gaussianPointBand p.1 p.2 (1/(2:ℝ)^k)))^2 ∂(gaussianRows d h).prod volume) ≤
      ENNReal.ofReal ((4*gaussianVectorBandConstant*(1/(2:ℝ)^k)^2)^h)*
        (ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1) := by
  let r : ℝ := 1/(2:ℝ)^k
  let C : ℝ≥0∞ := ENNReal.ofReal ((4*gaussianVectorBandConstant*r^2)^h)
  let B : ℝ≥0∞ := ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1
  have hC := gaussianVectorBandConstant_pos
  have hp (x : Space d) : (∫⁻ y, ENNReal.ofReal ((1/(dist x y+r))^(h:ℝ)) ∂μ) ≤ B :=
    regularized_potential_global μ x hK (Nat.cast_nonneg _) hq k hmass (hball x)
  apply (gaussian_point_band_second_moment μ (by positivity)).trans
  calc
    _ ≤ ∫⁻ z : Space d × Space d,
        ENNReal.ofReal ((4*gaussianVectorBandConstant*r^2/(dist z.1 z.2+r))^h) ∂μ.prod μ :=
      lintegral_mono (fun z => gaussian_point_pair_kernel z.1 z.2 (by dsimp [r]; positivity))
    _ = C * ∫⁻ z : Space d × Space d,
        ENNReal.ofReal ((1/(dist z.1 z.2+r))^(h:ℝ)) ∂μ.prod μ := by
      rw [← lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      rw [Real.rpow_natCast,← ENNReal.ofReal_mul (by positivity),← mul_pow]
      congr 2
      ring
    _ = C * ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((1/(dist x y+r))^(h:ℝ)) ∂μ ∂μ := by
      rw [lintegral_prod _ (by fun_prop)]
    _ ≤ C * ∫⁻ _ : Space d, B ∂μ := mul_le_mul_right (lintegral_mono hp) C
    _ = C*(B*μ univ) := by rw [lintegral_const]
    _ ≤ C*(B*1) := by gcongr
    _ = _ := by simp [C,B,r]

end Falconer

end OAI
