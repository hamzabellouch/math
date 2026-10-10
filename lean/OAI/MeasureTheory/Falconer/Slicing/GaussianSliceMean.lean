import OAI.MeasureTheory.Falconer.Slicing.GaussianBandLower
import OAI.MeasureTheory.Falconer.Slicing.GaussianSliceMoment

namespace OAI

/-! # First moments of actual Gaussian direction slices -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianDirectionMass (ν : Measure (Sphere d))
    (r : ℝ) (A : Fin h → Space d) : ℝ≥0∞ :=
  ENNReal.ofReal (r^(-(h:ℝ)))*ν (gaussianDirectionBand A r)

theorem gaussian_direction_band_first_moment (ν : Measure (Sphere d)) [SFinite ν] (r : ℝ) :
    (∫⁻ A : Fin h → Space d, ν (gaussianDirectionBand A r) ∂gaussianRows d h) =
      ∫⁻ w : Sphere d, gaussianRows d h {A | ∀ i, |inner ℝ (w:Space d) (A i)| ≤ r} ∂ν := by
  let S : Set ((Fin h → Space d) × Sphere d) :=
    {p | ∀ i, |inner ℝ (p.2:Space d) (p.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  exact (Measure.prod_apply hS).symm.trans (Measure.prod_apply_symm hS)

theorem gaussian_direction_band_mean_lower (ν : Measure (Sphere d)) [SFinite ν]
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ENNReal.ofReal ((gaussianBandLowerConstant*r)^h)*ν univ ≤
      ∫⁻ A : Fin h → Space d, ν (gaussianDirectionBand A r) ∂gaussianRows d h := by
  rw [gaussian_direction_band_first_moment,← lintegral_const]
  exact lintegral_mono (fun w => gaussianRows_one_band_lower (sphere_norm w) hr hr1)

theorem gaussian_direction_band_mean_upper (ν : Measure (Sphere d)) [SFinite ν]
    {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ A : Fin h → Space d, ν (gaussianDirectionBand A r) ∂gaussianRows d h) ≤
      ENNReal.ofReal ((gaussianBandConstant*r)^h)*ν univ := by
  rw [gaussian_direction_band_first_moment,← lintegral_const]
  exact lintegral_mono (fun w => gaussianRows_one_band (sphere_norm w) hr)

theorem gaussian_band_normalization {r C : ℝ} (hr : 0 < r) (_hC : 0 ≤ C) :
    ENNReal.ofReal (r^(-(h:ℝ)))*ENNReal.ofReal ((C*r)^h) = ENNReal.ofReal (C^h) := by
  rw [← ENNReal.ofReal_mul (by positivity),Real.rpow_neg hr.le,Real.rpow_natCast,mul_pow]
  congr 1
  field_simp

theorem gaussian_direction_mass_mean_lower (ν : Measure (Sphere d)) [SFinite ν]
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal (gaussianBandLowerConstant^h)*ν univ ≤
      ∫⁻ A : Fin h → Space d, gaussianDirectionMass ν r A ∂gaussianRows d h := by
  simp only [gaussianDirectionMass]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ = ENNReal.ofReal (r^(-(h:ℝ)))*
        (ENNReal.ofReal ((gaussianBandLowerConstant*r)^h)*ν univ) := by
      rw [← mul_assoc,gaussian_band_normalization hr gaussianBandLowerConstant_pos.le]
    _ ≤ _ := mul_le_mul_right (gaussian_direction_band_mean_lower ν hr.le hr1) _

theorem gaussian_direction_mass_mean_upper (ν : Measure (Sphere d)) [SFinite ν]
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ A : Fin h → Space d, gaussianDirectionMass ν r A ∂gaussianRows d h) ≤
      ENNReal.ofReal (gaussianBandConstant^h)*ν univ := by
  simp only [gaussianDirectionMass]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal (r^(-(h:ℝ)))*
        (ENNReal.ofReal ((gaussianBandConstant*r)^h)*ν univ) :=
      mul_le_mul_right (gaussian_direction_band_mean_upper ν hr.le) _
    _ = _ := by rw [← mul_assoc,gaussian_band_normalization hr gaussianBandConstant_pos.le]

end Falconer

end OAI
