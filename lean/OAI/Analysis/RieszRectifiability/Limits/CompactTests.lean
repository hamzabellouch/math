import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.MeanZero

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Function

def compactProjectedTest {d n : ℕ} (μ : Measure (Ambient d))
    (χ : Ambient d → ℝ) (π : Ambient d → Ambient n)
    (φ : Ambient n → ℝ) (η : Ambient d → ℝ) : Ambient d → ℝ :=
  meanCorrection μ (fun x => χ x * φ (π x)) η

theorem projected_cutoff_hasCompactSupport {d n : ℕ}
    (χ : Ambient d → ℝ) (π : Ambient d → Ambient n) (φ : Ambient n → ℝ)
    (hχ : HasCompactSupport χ) :
    HasCompactSupport (fun x => χ x * φ (π x)) := hχ.mul_right

theorem compactProjectedTest_hasCompactSupport {d n : ℕ}
    (μ : Measure (Ambient d)) (χ : Ambient d → ℝ) (π : Ambient d → Ambient n)
    (φ : Ambient n → ℝ) (η : Ambient d → ℝ)
    (hχ : HasCompactSupport χ) (hη : HasCompactSupport η) :
    HasCompactSupport (compactProjectedTest μ χ π φ η) := by
  have hc : HasCompactSupport (fun x =>
      ((∫ y, χ y * φ (π y) ∂μ) / (∫ y, η y ∂μ)) * η x) := hη.mul_left
  exact (projected_cutoff_hasCompactSupport χ π φ hχ).sub hc

theorem compactProjectedTest_continuous {d n : ℕ}
    (μ : Measure (Ambient d)) (χ : Ambient d → ℝ) (π : Ambient d → Ambient n)
    (φ : Ambient n → ℝ) (η : Ambient d → ℝ)
    (hχ : Continuous χ) (hπ : Continuous π) (hφ : Continuous φ)
    (hη : Continuous η) : Continuous (compactProjectedTest μ χ π φ η) :=
  (hχ.mul (hφ.comp hπ)).sub (continuous_const.mul hη)

theorem compactProjectedTest_integrable {d n : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (χ : Ambient d → ℝ) (π : Ambient d → Ambient n)
    (φ : Ambient n → ℝ) (η : Ambient d → ℝ)
    (hχ : Continuous χ) (hπ : Continuous π) (hφ : Continuous φ)
    (hη : Continuous η) (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η) :
    Integrable (compactProjectedTest μ χ π φ η) μ :=
  (compactProjectedTest_continuous μ χ π φ η hχ hπ hφ hη).integrable_of_hasCompactSupport
    (compactProjectedTest_hasCompactSupport μ χ π φ η hcχ hcη)

theorem compactProjectedTest_integral_zero {d n : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (χ : Ambient d → ℝ) (π : Ambient d → Ambient n)
    (φ : Ambient n → ℝ) (η : Ambient d → ℝ)
    (hχ : Continuous χ) (hπ : Continuous π) (hφ : Continuous φ)
    (hη : Continuous η) (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hne : (∫ x, η x ∂μ) ≠ 0) :
    (∫ x, compactProjectedTest μ χ π φ η x ∂μ) = 0 :=
  meanCorrection_integral_zero μ _ η
    ((hχ.mul (hφ.comp hπ)).integrable_of_hasCompactSupport
      (projected_cutoff_hasCompactSupport χ π φ hcχ))
    (hη.integrable_of_hasCompactSupport hcη) hne

theorem compactProjectedTest_eq_of_cutoff_one {d n : ℕ}
    (μ : Measure (Ambient d)) (χ : Ambient d → ℝ) (π : Ambient d → Ambient n)
    (φ : Ambient n → ℝ) (η : Ambient d → ℝ) (x : Ambient d)
    (hχ : χ x = 1) :
    compactProjectedTest μ χ π φ η x = φ (π x) -
      ((∫ y, χ y * φ (π y) ∂μ) / (∫ y, η y ∂μ)) * η x := by
  simp only [compactProjectedTest, meanCorrection, hχ, one_mul]

end

end RieszRectifiability

end OAI
