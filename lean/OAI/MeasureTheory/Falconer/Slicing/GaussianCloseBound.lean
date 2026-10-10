import OAI.MeasureTheory.Falconer.Slicing.GaussianCloseMass

namespace OAI

/-! # Finite-scale close-pair bounds for normalized direction slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_direction_close_frostman (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : ν univ ≤ 1)
    (hball : ∀ w : Sphere d, ∀ n : ℕ, n ≤ N →
      ν (ball w (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d)) :
    (∫⁻ A : Fin h → Space d,
      gaussianDirectionCloseMass ν A (1/(2:ℝ)^N) (1/(2:ℝ)^g) ∂gaussianRows d h) ≤
      ENNReal.ofReal ((2*gaussianPairBandConstant*(1/(2:ℝ)^N)^2)^h)*
        ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
          (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q)))) := by
  let r : ℝ := 1/(2:ℝ)^N
  let D : Set (Sphere d × Sphere d) := {z | dist z.1 z.2 < 1/(2:ℝ)^g}
  let C := ENNReal.ofReal ((2*gaussianPairBandConstant*r^2)^h)
  let B := ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
    (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))
  rw [gaussian_direction_close_average]
  calc
    _ ≤ ∫⁻ z in D, ENNReal.ofReal
        ((2*gaussianPairBandConstant*r^2/(dist z.1 z.2+r))^h) ∂ν.prod ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hchart] with z hz
      simpa only [Subtype.dist_eq] using gaussianRows_pair_band_chart (h := h)
        (sphere_norm z.1) (sphere_norm z.2) hz (by positivity)
    _ = C * ∫⁻ z in D, ENNReal.ofReal ((1/(dist z.1 z.2+r))^(h:ℝ)) ∂ν.prod ν := by
      rw [← lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      rw [gaussian_pair_kernel_factor,ENNReal.ofReal_mul
        (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          gaussianPairBandConstant_pos.le) (sq_nonneg r)) h)]
    _ ≤ C*B := mul_le_mul_right
      (regularized_pair_potential ν hK (Nat.cast_nonneg _) hq g N hg hmass hball) C

theorem gaussian_direction_slice_close_frostman (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : ν univ ≤ 1)
    (hball : ∀ w : Sphere d, ∀ n : ℕ, n ≤ N →
      ν (ball w (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d)) :
    (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).prod
        (gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)))
          {z | dist z.1 z.2 < 1/(2:ℝ)^g} ∂gaussianRows d h) ≤
      ENNReal.ofReal ((2*gaussianPairBandConstant)^h)*
        ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
          (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q)))) := by
  simp_rw [gaussianDirectionSlice_close_identity]
  rw [lintegral_const_mul' _ _ (by
    rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply (mul_le_mul_right (gaussian_direction_close_frostman ν hK hq g N hg hmass hball hchart) _).trans_eq
  rw [← mul_assoc,gaussian_squared_band_normalization (by positivity)
    (mul_nonneg (by norm_num) gaussianPairBandConstant_pos.le)]

end Falconer

end OAI
