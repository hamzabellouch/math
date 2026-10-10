import OAI.MeasureTheory.Falconer.Slicing.GaussianSliceMass
import OAI.MeasureTheory.Falconer.Measures.DensityTruncation

namespace OAI

/-! # Direction-slice mass deletion using the proved second moment -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_direction_mass_tail (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {r : ℝ} {T B : ℝ≥0∞} (hT : 0 < T) (hTtop : T ≠ ∞)
    (hmoment : (∫⁻ A : Fin h → Space d, (gaussianDirectionMass ν r A)^2
      ∂gaussianRows d h) ≤ B) :
    (∫⁻ A in {A : Fin h → Space d | T < gaussianDirectionMass ν r A},
      gaussianDirectionMass ν r A ∂gaussianRows d h) ≤ T⁻¹*B := by
  have hm := gaussianDirectionMass_measurable (h := h) ν r
  have hh := density_tail_mass (gaussianRows d h) (gaussianDirectionMass ν r) hm
    (p := 2) hT hTtop (by norm_num)
  rw [withDensity_apply _ (measurableSet_lt measurable_const hm)] at hh
  norm_num only [show (1-(2:ℝ)) = -1 by norm_num,ENNReal.rpow_neg_one,ENNReal.rpow_two] at hh
  exact hh.trans (mul_le_mul_right hmoment _)

end Falconer

end OAI
