import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTailLinear
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralColumnRank
import Mathlib.Analysis.Analytic.Constructions

namespace OAI

/-! Complex-linear coefficient operators and their polynomial dependence on the spectral parameter. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def circularFieldBounded (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ →ᵇ ℂ) (v : CircularTailSpace) : CircularTailSpace :=
  boundedCircularSource (circularFieldBound νp νm η m ‖q‖) 0
    (circularFieldBound_nonneg νp νm η m ‖q‖)
    (fun t z => circularBoundedField νp νm η m (q t) z)
    ((circularBoundedField_continuous νp νm η m).comp
      ((q.continuous.comp continuous_fst).prodMk continuous_snd))
    (fun t => by rw [circularBoundedField_zero,norm_zero])
    (fun t z w => circularBoundedField_difference νp νm η m hm ‖q‖ (q t)
      (q.norm_coe_le_norm t) z w) v

theorem circularFieldBounded_evaluation (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ →ᵇ ℂ) (v : CircularTailSpace) (t : ℝ) :
    circularTailEvaluation (circularFieldBounded νp νm η m hm q v) t=
      circularBoundedField νp νm η m (q t) (circularTailEvaluation v t) := rfl

theorem circularFieldBounded_norm (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ →ᵇ ℂ) (v : CircularTailSpace) :
    ‖circularFieldBounded νp νm η m hm q v‖ ≤ circularFieldBound νp νm η m ‖q‖*‖v‖ := by
  apply max_le
  · apply (BoundedContinuousFunction.norm_le (mul_nonneg (circularFieldBound_nonneg νp νm η m ‖q‖) (norm_nonneg v))).2
    intro t
    exact (norm_fst_le _).trans ((circularBoundedField_norm νp νm η m hm ‖q‖ (q t)
      (q.norm_coe_le_norm t) _).trans (mul_le_mul_of_nonneg_left
      (circularTailEvaluation_norm v t) (circularFieldBound_nonneg νp νm η m ‖q‖)))
  · apply (BoundedContinuousFunction.norm_le (mul_nonneg (circularFieldBound_nonneg νp νm η m ‖q‖) (norm_nonneg v))).2
    intro t
    exact (norm_snd_le _).trans ((circularBoundedField_norm νp νm η m hm ‖q‖ (q t)
      (q.norm_coe_le_norm t) _).trans (mul_le_mul_of_nonneg_left
      (circularTailEvaluation_norm v t) (circularFieldBound_nonneg νp νm η m ‖q‖)))

noncomputable def circularFieldOperator (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ →ᵇ ℂ) : CircularTailSpace →L[ℂ] CircularTailSpace :=
  LinearMap.mkContinuous
    { toFun := circularFieldBounded νp νm η m hm q
      map_add' := by
        intro v w
        apply Prod.ext
        · apply BoundedContinuousFunction.ext
          intro t
          exact congrArg Prod.fst (circularBoundedField_add νp νm η m (q t)
            (circularTailEvaluation v t) (circularTailEvaluation w t))
        · apply BoundedContinuousFunction.ext
          intro t
          exact congrArg Prod.snd (circularBoundedField_add νp νm η m (q t)
            (circularTailEvaluation v t) (circularTailEvaluation w t))
      map_smul' := by
        intro a v
        apply Prod.ext
        · apply BoundedContinuousFunction.ext
          intro t
          exact congrArg Prod.fst (circularBoundedField_smul νp νm η m (q t) a
            (circularTailEvaluation v t))
        · apply BoundedContinuousFunction.ext
          intro t
          exact congrArg Prod.snd (circularBoundedField_smul νp νm η m (q t) a
            (circularTailEvaluation v t)) }
    (circularFieldBound νp νm η m ‖q‖) (circularFieldBounded_norm νp νm η m hm q)

theorem circularFieldOperator_evaluation (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ →ᵇ ℂ) (v : CircularTailSpace) (t : ℝ) :
    circularTailEvaluation (circularFieldOperator νp νm η m hm q v) t=
      circularBoundedField νp νm η m (q t) (circularTailEvaluation v t) := rfl

theorem circularFieldOperator_norm (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ →ᵇ ℂ) :
    ‖circularFieldOperator νp νm η m hm q‖ ≤ circularFieldBound νp νm η m ‖q‖ := by
  exact LinearMap.mkContinuous_norm_le _ (circularFieldBound_nonneg νp νm η m ‖q‖) _

end DefocusingNLS

end OAI
