import OAI.MeasureTheory.Falconer.Slicing.GaussianIncidenceAverage
import OAI.MeasureTheory.Falconer.Slicing.GaussianSliceTail

namespace OAI

/-! # Incidence cost of deleting rows with excessive direction mass -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_slice_incidence_per_row_upper
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space d × Sphere d)) (A : Fin h → Space d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ z : Space h, (gaussianPointSliceMeasure μ A z r).prod
      (gaussianDirectionSliceMeasure ν A r) E) ≤
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*gaussianDirectionMass ν r A := by
  have he : gaussianDirectionSliceMeasure ν A r univ = gaussianDirectionMass ν r A := by
    simp [gaussianDirectionSliceMeasure,gaussianDirectionMass,Measure.smul_apply]
  calc
    _ ≤ ∫⁻ z : Space h, (gaussianPointSliceMeasure μ A z r).prod
        (gaussianDirectionSliceMeasure ν A r) univ := lintegral_mono (fun _ => measure_mono (subset_univ _))
    _ = ∫⁻ z : Space h, gaussianPointMass μ r (A,z)*gaussianDirectionMass ν r A := by
      rw [← univ_prod_univ]
      simp only [Measure.prod_prod,gaussianPointSliceMeasure_univ,he]
    _ = (∫⁻ z : Space h, gaussianPointMass μ r (A,z))*gaussianDirectionMass ν r A := by
      apply lintegral_mul_const'
      rw [← he]
      exact (measure_lt_top _ _).ne
    _ = _ := by rw [gaussianPointMass_integrated μ A hr]

theorem gaussian_slice_incidence_mass_tail
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space d × Sphere d)) {r : ℝ} (hr : 0 < r)
    {T B : ℝ≥0∞} (hT : 0 < T) (hTtop : T ≠ ∞)
    (hmoment : (∫⁻ A : Fin h → Space d, (gaussianDirectionMass ν r A)^2 ∂gaussianRows d h) ≤ B) :
    (∫⁻ A in {A : Fin h → Space d | T < gaussianDirectionMass ν r A},
      (∫⁻ z : Space h, (gaussianPointSliceMeasure μ A z r).prod
        (gaussianDirectionSliceMeasure ν A r) E) ∂gaussianRows d h) ≤
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(T⁻¹*B) := by
  calc
    _ ≤ ∫⁻ A in {A : Fin h → Space d | T < gaussianDirectionMass ν r A},
        (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*gaussianDirectionMass ν r A ∂gaussianRows d h :=
      lintegral_mono (fun A => gaussian_slice_incidence_per_row_upper μ ν E A hr)
    _ = (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*
        ∫⁻ A in {A : Fin h → Space d | T < gaussianDirectionMass ν r A},
          gaussianDirectionMass ν r A ∂gaussianRows d h :=
      lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_lt_top _ _).ne)
    _ ≤ _ := mul_le_mul_right (gaussian_direction_mass_tail ν hT hTtop hmoment) _

end Falconer

end OAI
