import OAI.MeasureTheory.Falconer.Slicing.GaussianSliceMean
import OAI.MeasureTheory.Falconer.Slicing.GaussianSliceBound

namespace OAI

/-! # Normalized direction-slice masses and their second moment -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianDirectionMass_measurable (ν : Measure (Sphere d)) [SFinite ν] (r : ℝ) :
    Measurable (gaussianDirectionMass (h := h) ν r) := by
  apply Measurable.const_mul
  let S : Set ((Fin h → Space d) × Sphere d) :=
    {p | ∀ i, |inner ℝ (p.2:Space d) (p.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  exact measurable_measure_prodMk_left hS

theorem gaussian_squared_band_normalization {r C : ℝ} (hr : 0 < r) (_hC : 0 ≤ C) :
    (ENNReal.ofReal (r^(-(h:ℝ))))^2*ENNReal.ofReal ((C*r^2)^h) =
      ENNReal.ofReal (C^h) := by
  rw [← ENNReal.ofReal_pow (by positivity),← ENNReal.ofReal_mul (by positivity),
    Real.rpow_neg hr.le,Real.rpow_natCast,mul_pow]
  congr 1
  have he : (r^2)^h = (r^h)^2 := by
    simp only [← pow_mul]
    congr 1
    omega
  rw [he]
  field_simp

theorem gaussian_direction_mass_second_moment
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (k : ℕ)
    (hmass : ν univ ≤ 1)
    (hball : ∀ w : Sphere d, ∀ n : ℕ, n ≤ k →
      ν (ball w (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d)) :
    (∫⁻ A : Fin h → Space d,
      (gaussianDirectionMass ν (1/(2:ℝ)^k) A)^2 ∂gaussianRows d h) ≤
      ENNReal.ofReal ((2*gaussianPairBandConstant)^h)*
        (ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1) := by
  simp only [gaussianDirectionMass,mul_pow]
  rw [lintegral_const_mul' _ _ (by
    rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  calc
    _ ≤ (ENNReal.ofReal ((1/(2:ℝ)^k)^(-(h:ℝ))))^2*
        (ENNReal.ofReal ((2*gaussianPairBandConstant*(1/(2:ℝ)^k)^2)^h)*
          (ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1)) := by
      exact mul_le_mul_right
        (gaussian_direction_second_moment_frostman ν hK hq k hmass hball hchart) _
    _ = _ := by
      rw [← mul_assoc,gaussian_squared_band_normalization (by positivity)
        (mul_nonneg (by norm_num) gaussianPairBandConstant_pos.le)]
      rw [mul_pow]

end Falconer

end OAI
