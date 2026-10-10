import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinParameterMoments
import OAI.Probability.SKBarriers.SpinGlass.SpinCoefficientVariation

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem spinPressure_hasDerivAt_curve {N : ℕ} (d : ℕ)
    (I : Fin d → Finset (Fin N)) (m : Fin d → ℝ)
    (c : ℝ → Fin d → ℝ) {t : ℝ} {c' : Fin d → ℝ} (hc : HasDerivAt c c' t) :
    HasDerivAt (fun u =>
      hierarchyPressure d m (affineLogPartition (fun _ => 0) (spinExponent d (c u) I)) 0)
      (∑ i : Fin d, c' i*(c t i*(1-∑ j : Fin (d+1), if i.val < j.val then hierarchyAtom d m 1 j *
        (∫ z, (hierarchySpinMean d m (spinExponent d (c t) I) (fun s => spinMonomial s (I i)) j z)^2
          ∂hierarchyPathLaw d m (affineLogPartition (fun _ => 0) (spinExponent d (c t) I)) 0) else 0))) t := by
  have hd := (parameter_contDiff_at_field (spinPressure_paramRegular d I (fun _ => 0) m).1 (0:ℝ)).differentiable (by decide)
  have H := (hd (c t)).hasFDerivAt.comp_hasDerivAt t hc
  apply H.congr_deriv
  symm
  conv_rhs => rw [pi_eq_sum_univ' c',map_sum]
  simp only [map_smul,smul_eq_mul,spinPressure_coefficient_variation]
end SK.Analytic

end
end

end

end OAI
