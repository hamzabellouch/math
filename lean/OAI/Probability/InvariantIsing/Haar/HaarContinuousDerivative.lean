import OAI.Probability.InvariantIsing.Haar.HaarPolynomialValue

namespace OAI

/-! Compact domination for continuous derivatives along actual Haar rotations. -/
noncomputable section
open Matrix MeasureTheory
namespace InvariantIsing

lemma continuous_haar_integrable {N : ℕ} (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) : Integrable f μ := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.measurable.aestronglyMeasurable B
    (ae_of_all μ fun U => hB U (Set.mem_univ U))

lemma integral_haar_continuous_derivative {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (i j : Fin N)
    (f q : SpecialOrthogonal N → ℝ) (hf : Continuous f) (hq : Continuous q)
    (hd : ∀ U : SpecialOrthogonal N, ∀ t : ℝ,
      HasDerivAt (fun s => f (specialPlaneRotation i j s*U))
        (q (specialPlaneRotation i j t*U)) t) :
    (∫ U, q U ∂μ) = 0 := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hq.continuousOn
  have he := integral_special_rotation_derivative_eq_zero μ
    (specialPlaneRotation i j) (specialPlaneRotation_zero i j) f hf.measurable
    (continuous_haar_integrable μ f hf) (fun t U => q (specialPlaneRotation i j t*U))
    (by simpa only [specialPlaneRotation_zero,one_mul] using hq.measurable.aestronglyMeasurable)
    (fun _ => B) (integrable_const B)
    (ae_of_all μ fun U t _ => hB (specialPlaneRotation i j t*U) (Set.mem_univ _))
    (ae_of_all μ fun U t _ => hd U t)
  simpa only [specialPlaneRotation_zero,one_mul] using he

end InvariantIsing

end

end OAI
