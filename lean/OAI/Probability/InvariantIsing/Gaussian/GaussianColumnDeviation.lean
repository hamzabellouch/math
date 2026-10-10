import OAI.Probability.InvariantIsing.Gaussian.GaussianColumnResolventContinuity
import OAI.Probability.InvariantIsing.Spectral.PositiveResolventFluctuation

namespace OAI

/-! Integrability of the actual leave-one-column quadratic deviation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace InvariantIsing

def gaussianGramColumnDeviation {N m : ℕ} (t : ℝ) (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) : ℝ := |gaussianGramColumnQuadratic t z j-(gaussianGramLeaveResolvent t z j).trace/N|

lemma continuous_gaussianGramColumnDeviation {N m : ℕ} {t : ℝ} (ht : 0 < t) (j : Fin m) :
    Continuous (gaussianGramColumnDeviation (N := N) t · j) :=
  ((continuous_gaussianGramColumnQuadratic ht j).sub
    ((continuous_gaussianGramLeaveResolvent ht j).matrix_trace.div_const _)).abs

lemma gaussianGramColumnDeviation_bound {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (g : Fin m → Fin N → ℝ) (j : Fin m) :
    gaussianGramColumnDeviation t (gaussianColumnArray g) j ≤
      (1/((N : ℝ)*t))*‖WithLp.toLp 2 (g j)‖^2+1/t := by
  unfold gaussianGramColumnDeviation
  rw [gaussianGramColumnQuadratic_eq]
  exact positiveResolvent_normalized_abs_bound hN ht
    (gaussianGramLeaveOneOut_posSemidef (gaussianColumnArray g) j) _

lemma gaussianGramColumnDeviation_integrable {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (j : Fin m) : Integrable (fun g : Fin m → Fin N → ℝ =>
      gaussianGramColumnDeviation t (gaussianColumnArray g) j)
      (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin N => gaussianReal 0 1))) := by
  have hi := (measurePreserving_eval
    (fun _ : Fin m => Measure.pi (fun _ : Fin N => gaussianReal 0 1)) j).hasLaw.integrable_comp
      (gaussianCoordinateVector_sq_integrable (id : Fin N → Fin N))
  have hm : AEStronglyMeasurable (fun g : Fin m → Fin N → ℝ =>
      gaussianGramColumnDeviation t (gaussianColumnArray g) j)
      (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin N => gaussianReal 0 1))) :=
    ((continuous_gaussianGramColumnDeviation (N := N) ht j).comp
    (continuous_gaussianColumnArray (N := N) (m := m))).aestronglyMeasurable
  apply ((hi.const_mul (1/((N : ℝ)*t))).add (integrable_const (1/t))).mono' hm
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ gaussianGramColumnDeviation t (gaussianColumnArray g) j from abs_nonneg _)]
  exact gaussianGramColumnDeviation_bound hN ht g j

end InvariantIsing

end

end OAI
