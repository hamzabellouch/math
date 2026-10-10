import OAI.MeasureTheory.Falconer.Slicing.GaussianPointBound

namespace OAI

/-! # Normalized point slices in Gaussian row coordinates -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianPointSliceMeasure (μ : Measure (Space d))
    (A : Fin h → Space d) (z : Space h) (r : ℝ) : Measure (Space d) :=
  ENNReal.ofReal (r^(-(h:ℝ))) • μ.restrict (gaussianPointBand A z r)

noncomputable def gaussianPointMass (μ : Measure (Space d)) (r : ℝ)
    (p : (Fin h → Space d) × Space h) : ℝ≥0∞ :=
  ENNReal.ofReal (r^(-(h:ℝ)))*μ (gaussianPointBand p.1 p.2 r)

theorem gaussianPointSliceMeasure_univ (μ : Measure (Space d))
    (A : Fin h → Space d) (z : Space h) (r : ℝ) :
    gaussianPointSliceMeasure μ A z r univ = gaussianPointMass μ r (A,z) := by
  simp [gaussianPointSliceMeasure,gaussianPointMass,Measure.smul_apply]

theorem gaussianPointMass_measurable (μ : Measure (Space d)) [SFinite μ] (r : ℝ) :
    Measurable (gaussianPointMass (h := h) μ r) := by
  apply Measurable.const_mul
  let S : Set (((Fin h → Space d) × Space h) × Space d) :=
    {p | p.2 ∈ gaussianPointBand p.1.1 p.1.2 r}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : ((Fin h → Space d) × Space h) × Space d |
      ∀ i, |inner ℝ p.2 (p.1.1 i)-p.1.2 i| ≤ r}
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  exact measurable_measure_prodMk_left hS

theorem gaussianPointMass_integrated (μ : Measure (Space d)) [SFinite μ]
    (A : Fin h → Space d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ z : Space h, gaussianPointMass μ r (A,z)) = ENNReal.ofReal ((2:ℝ)^h)*μ univ := by
  simp only [gaussianPointMass]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,gaussianPointBand_integrated_mass μ A hr.le,
    ← mul_assoc,gaussian_band_normalization hr (by norm_num : (0:ℝ) ≤ 2)]

theorem gaussian_point_mass_second_moment (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (k : ℕ)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : Space d, ∀ n : ℕ, n ≤ k →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      (gaussianPointMass μ (1/(2:ℝ)^k) p)^2 ∂(gaussianRows d h).prod volume) ≤
      ENNReal.ofReal ((4*gaussianVectorBandConstant)^h)*
        (ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1) := by
  simp only [gaussianPointMass,mul_pow]
  rw [lintegral_const_mul' _ _ (by
    rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  calc
    _ ≤ (ENNReal.ofReal ((1/(2:ℝ)^k)^(-(h:ℝ))))^2*
        (ENNReal.ofReal ((4*gaussianVectorBandConstant*(1/(2:ℝ)^k)^2)^h)*
          (ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1)) :=
      mul_le_mul_right (gaussian_point_band_second_moment_frostman μ hK hq k hmass hball) _
    _ = _ := by
      rw [← mul_assoc,gaussian_squared_band_normalization (by positivity)
        (mul_nonneg (by norm_num) gaussianVectorBandConstant_pos.le),mul_pow]

end Falconer

end OAI
