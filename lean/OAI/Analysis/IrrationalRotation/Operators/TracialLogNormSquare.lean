import OAI.Analysis.IrrationalRotation.Operators.TracialLogDerivative
import OAI.Analysis.IrrationalRotation.Operators.TracialNormSquareDerivative
import OAI.Analysis.IrrationalRotation.Analysis.StrictlyPositiveNormalization

namespace OAI

noncomputable section
namespace Invariant233
namespace CFCLogSeries
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]

theorem hasDerivAt_re_trace_log_normSquare_of_normalization (τ : TracialState A)
    {f f' : ℝ → A} (hunit : ∀ y, IsUnit (f y))
    (hf : ∀ y, HasDerivAt f (f' y) y) {x : ℝ} (hcf' : ContinuousAt f' x)
    (hscale : ∃ c : ℝ, 0 < c ∧ ‖1-c • (star (f x) * f x)‖ < 1) :
    HasDerivAt (fun y => (τ (CFC.log (star (f y) * f y))).re)
      (2 * (τ (Ring.inverse (f x) * f' x)).re) x := by
  have hp : ∀ y, IsStrictlyPositive (star (f y) * f y) :=
    fun y => ⟨star_mul_self_nonneg _, (hunit y).star.mul (hunit y)⟩
  have hq' : ContinuousAt (fun y => star (f' y) * f y + star (f y) * f' y) x :=
    (hcf'.star.mul (hf x).continuousAt).add ((hf x).continuousAt.star.mul hcf')
  have hlog := hasDerivAt_trace_log_of_normalization τ hp
    (fun y => TracialState.hasDerivAt_normSquare (hf y)) hq' hscale
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hlog
  change HasDerivAt (fun y => (τ (CFC.log (star (f y) * f y))).re)
    (τ (Ring.inverse (star (f x) * f x) *
      (star (f' x) * f x + star (f x) * f' x))).re x at hre
  exact hre.congr_deriv (τ.re_inverse_normSquare_differential (f x) (f' x) (hunit x))

theorem hasDerivAt_re_trace_log_normSquare (τ : TracialState A)
    {f f' : ℝ → A} (hunit : ∀ y, IsUnit (f y))
    (hf : ∀ y, HasDerivAt f (f' y) y) {x : ℝ} (hcf' : ContinuousAt f' x) :
    HasDerivAt (fun y => (τ (CFC.log (star (f y) * f y))).re)
      (2 * (τ (Ring.inverse (f x) * f' x)).re) x :=
  hasDerivAt_re_trace_log_normSquare_of_normalization τ hunit hf hcf'
    (exists_pos_norm_one_sub_smul_lt_one
      ⟨star_mul_self_nonneg _, (hunit x).star.mul (hunit x)⟩)

end CFCLogSeries
end Invariant233

end

end OAI
