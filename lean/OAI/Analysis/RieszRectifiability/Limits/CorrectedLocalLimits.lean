import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.MeanCorrectionAdmissible
import OAI.Analysis.RieszRectifiability.Kernel.CorrectedSingularTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

theorem globally_corrected_local_singular_limit {d : ℕ} (m : ℕ)
    (μ : ℕ → Measure (Ambient d)) (s : Set (Ambient d))
    (w : ℕ → Ambient d → ℝ) (φ η : Ambient d → ℝ)
    (hc : Tendsto (fun j => (∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)) atTop (𝓝 0))
    (hφ : ∀ j, Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m (w j) φ q.1 q.2)
      (((μ j).restrict s).prod ((μ j).restrict s)))
    (hη : ∀ j, Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m (w j) η q.1 q.2)
      (((μ j).restrict s).prod ((μ j).restrict s)))
    (P Q : ℝ)
    (hP : Tendsto (fun j => ∫ q : Ambient d × Ambient d, fractionalBilinear m (w j) φ q.1 q.2
      ∂((μ j).restrict s).prod ((μ j).restrict s)) atTop (𝓝 P))
    (hQ : Tendsto (fun j => ∫ q : Ambient d × Ambient d, fractionalBilinear m (w j) η q.1 q.2
      ∂((μ j).restrict s).prod ((μ j).restrict s)) atTop (𝓝 Q)) :
    Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      fractionalBilinear m (w j) (meanCorrection (μ j) φ η) q.1 q.2
      ∂((μ j).restrict s).prod ((μ j).restrict s)) atTop (𝓝 P) := by
  have heq : ∀ j, (∫ q : Ambient d × Ambient d,
      fractionalBilinear m (w j) (meanCorrection (μ j) φ η) q.1 q.2
        ∂((μ j).restrict s).prod ((μ j).restrict s)) =
      (∫ q : Ambient d × Ambient d, fractionalBilinear m (w j) φ q.1 q.2
        ∂((μ j).restrict s).prod ((μ j).restrict s)) -
        ((∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)) *
          (∫ q : Ambient d × Ambient d, fractionalBilinear m (w j) η q.1 q.2
            ∂((μ j).restrict s).prod ((μ j).restrict s)) := by
    intro j
    exact fractionalBilinear_integral_test_sub m ((μ j).restrict s) (w j) φ η _ (hφ j) (hη j)
  simp only [heq]
  simpa only [zero_mul, sub_zero] using! hP.sub (hc.mul hQ)

end

end RieszRectifiability

end OAI
