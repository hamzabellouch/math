import OAI.Probability.InvariantIsing.Haar.HaarPolynomialRotation
import OAI.Probability.InvariantIsing.Haar.HaarCompactness

namespace OAI

/-! Bounded continuous polynomial observables on the physical rotation group. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

def haarPolynomialValue {N : ℕ} (p : MatrixPolynomial N) (U : SpecialOrthogonal N) : ℝ :=
  matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ) p

lemma continuous_haarPolynomialValue {N : ℕ} (p : MatrixPolynomial N) :
    Continuous (haarPolynomialValue p) := by
  have hm : Continuous (fun U : SpecialOrthogonal N =>
      fun ij : Fin N × Fin N => (U : Matrix (Fin N) (Fin N) ℝ) ij.1 ij.2) := by
    exact continuous_pi fun ij => (continuous_apply ij.2).comp
      ((continuous_apply ij.1).comp continuous_subtype_val)
  exact p.continuous_eval.comp hm

lemma haarPolynomialValue_bound {N : ℕ} (p : MatrixPolynomial N) :
    ∃ B : ℝ, ∀ U : SpecialOrthogonal N, ‖haarPolynomialValue p U‖ ≤ B := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_haarPolynomialValue p).continuousOn
  exact ⟨B,fun U => hB U (Set.mem_univ U)⟩

lemma haarPolynomialValue_integrable {N : ℕ} (p : MatrixPolynomial N)
    (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ] :
    Integrable (haarPolynomialValue p) μ := by
  obtain ⟨B,hB⟩ := haarPolynomialValue_bound p
  exact Integrable.of_bound (continuous_haarPolynomialValue p).measurable.aestronglyMeasurable
    B (ae_of_all μ hB)

/-- Infinitesimal Haar invariance, with the domination supplied by compactness. -/
theorem integral_haarPolynomialDerivation {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
    (p : MatrixPolynomial N) (i j : Fin N) :
    (∫ U, haarPolynomialValue (matrixPolynomialDerivation (planeGenerator i j) p) U ∂μ) = 0 := by
  let q := matrixPolynomialDerivation (planeGenerator i j) p
  obtain ⟨B,hB⟩ := haarPolynomialValue_bound q
  have he := integral_special_rotation_derivative_eq_zero μ
    (specialPlaneRotation i j) (specialPlaneRotation_zero i j)
    (haarPolynomialValue p) (continuous_haarPolynomialValue p).measurable
    (haarPolynomialValue_integrable p μ)
    (fun t U => haarPolynomialValue q (specialPlaneRotation i j t*U))
    (by simpa only [specialPlaneRotation_zero,one_mul] using
      (continuous_haarPolynomialValue q).measurable.aestronglyMeasurable)
    (fun _ => B) (integrable_const B)
    (ae_of_all μ fun U t _ => hB (specialPlaneRotation i j t*U))
    (ae_of_all μ fun U t _ => hasDerivAt_specialPlaneRotation_polynomial p i j U t)
  simpa only [specialPlaneRotation_zero,one_mul] using he

end InvariantIsing

end

end OAI
