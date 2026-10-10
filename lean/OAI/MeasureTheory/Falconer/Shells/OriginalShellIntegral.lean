import OAI.MeasureTheory.Falconer.Radial.RadialDistanceError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceAngularShellMeasure_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hpos : ∀ t, 0 ≤ Ψ t) (hzero : ∀ t ≤ 0, Ψ t = 0) (f : ℝ → E) :
    (∫ r, f r ∂sourceAngularShellMeasure v Ψ) =
      ((2:ℝ)^v)⁻¹ • ∫ r : ℝ, Ψ (r/(2:ℝ)^v) • f r := by
  have hR : 0 < (2:ℝ)^v := by positivity
  rw [sourceAngularShellMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hpos _) hR.le)]
  have he : (fun r => (Ψ (r/(2:ℝ)^v)/(2:ℝ)^v) • f r) =
      fun r => ((2:ℝ)^v)⁻¹ • (Ψ (r/(2:ℝ)^v) • f r) := by
    funext r
    rw [smul_smul]
    congr 1
    ring
  rw [he, integral_smul]
  congr 1
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : r ∈ Ioi (0:ℝ)
  · exact Set.indicator_of_mem hr _
  · have hz : Ψ (r/(2:ℝ)^v) = 0 := hzero _ (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hr) hR.le)
    simp [hr,hz]

theorem sourceRadialSquareEnergy_complex (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t) (hzero : ∀ t ≤ 0, Ψ t = 0)
    (F : ℝ → ℂ) :
    (sourceRadialSquareEnergy a v Ψ F : ℂ) =
      ((2:ℝ)^(2*(v-a))) • (((2:ℝ)^v)⁻¹ •
        ∫ r : ℝ, Ψ (r/(2:ℝ)^v) • ((‖F r‖^2 : ℝ) : ℂ)) := by
  rw [sourceRadialSquareEnergy, Complex.ofReal_mul, ← integral_complex_ofReal]
  rw [sourceAngularShellMeasure_integral v hΨ hpos hzero]
  rfl

end PlanarFalconer

end OAI
