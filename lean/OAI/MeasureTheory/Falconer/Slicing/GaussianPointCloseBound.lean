import OAI.MeasureTheory.Falconer.Slicing.GaussianPointClose

namespace OAI

/-! # Localized finite-scale second moments for point slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_close_frostman (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : Space d, ∀ n : ℕ, n ≤ N →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      gaussianPointCloseMass μ p (1/(2:ℝ)^N) (1/(2:ℝ)^g) ∂(gaussianRows d h).prod volume) ≤
      ENNReal.ofReal ((4*gaussianVectorBandConstant*(1/(2:ℝ)^N)^2)^h)*
        ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
          (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q)))) := by
  let r : ℝ := 1/(2:ℝ)^N
  let D : Set (Space d × Space d) := {z | dist z.1 z.2 < 1/(2:ℝ)^g}
  let C := ENNReal.ofReal ((4*gaussianVectorBandConstant*r^2)^h)
  let B := ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
    (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))
  have hC := gaussianVectorBandConstant_pos
  apply (gaussian_point_close_average μ (by positivity) (1/(2:ℝ)^g)).trans
  calc
    _ ≤ ∫⁻ z in D, ENNReal.ofReal
        ((4*gaussianVectorBandConstant*r^2/(dist z.1 z.2+r))^h) ∂μ.prod μ :=
      lintegral_mono (fun z => gaussian_point_pair_kernel z.1 z.2 (by dsimp [r]; positivity))
    _ = C * ∫⁻ z in D, ENNReal.ofReal ((1/(dist z.1 z.2+r))^(h:ℝ)) ∂μ.prod μ := by
      rw [← lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      rw [Real.rpow_natCast,← ENNReal.ofReal_mul (by positivity),← mul_pow]
      congr 2
      ring
    _ ≤ C*B := mul_le_mul_right
      (regularized_pair_potential μ hK (Nat.cast_nonneg _) hq g N hg hmass hball) C

theorem gaussian_point_slice_close_frostman (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : Space d, ∀ n : ℕ, n ≤ N →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 (1/(2:ℝ)^N)).prod
        (gaussianPointSliceMeasure μ p.1 p.2 (1/(2:ℝ)^N)))
          {z | dist z.1 z.2 < 1/(2:ℝ)^g} ∂(gaussianRows d h).prod volume) ≤
      ENNReal.ofReal ((4*gaussianVectorBandConstant)^h)*
        ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
          (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q)))) := by
  simp_rw [gaussianPointSlice_close_identity]
  rw [lintegral_const_mul' _ _ (by
    rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply (mul_le_mul_right (gaussian_point_close_frostman μ hK hq g N hg hmass hball) _).trans_eq
  rw [← mul_assoc,gaussian_squared_band_normalization (by positivity)
    (mul_nonneg (by norm_num) gaussianVectorBandConstant_pos.le)]

end Falconer

end OAI
