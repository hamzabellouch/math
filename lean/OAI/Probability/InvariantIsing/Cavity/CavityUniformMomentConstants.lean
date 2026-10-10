import OAI.Probability.InvariantIsing.Cavity.CavityContinuousCutoff
import OAI.Probability.InvariantIsing.Cavity.CavityLinearGaussianMoment

namespace OAI

/-! The constants in the cutoff estimates are uniform over compact sets
of cavity blocks, as required before the geometric limit is taken. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace InvariantIsing

lemma continuous_cavityMatrixMass (d k : ℕ) :
    Continuous (cavityMatrixMass : Matrix (Fin d) (Fin k) ℝ → ℝ) := by
  unfold cavityMatrixMass
  fun_prop

lemma continuous_cavityFactorSize (d k : ℕ) :
    Continuous (fun p : CavityFactorBlocks d k => cavityFactorSize p.1 p.2.1 p.2.2) := by
  exact (((continuous_cavityMatrixMass d d).comp continuous_fst).add
    ((continuous_cavityMatrixMass d k).comp (continuous_fst.comp continuous_snd))).add
      ((continuous_cavityMatrixMass k k).comp (continuous_snd.comp continuous_snd))

theorem cavity_compact_factor_size_bound {d k : ℕ} (S : Set (CavityFactorBlocks d k))
    (hS : IsCompact S) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p ∈ S, cavityFactorSize p.1 p.2.1 p.2.2 ≤ D := by
  obtain ⟨D, hD⟩ := hS.exists_bound_of_continuousOn (continuous_cavityFactorSize d k).continuousOn
  refine ⟨max D 0, le_max_right _ _, fun p hp => ?_⟩
  exact (le_abs_self _).trans ((hD p hp).trans (le_max_left _ _))

theorem cavityGaussianLinearMomentBound_mono (d p : ℕ) {c C M : ℝ} (hc : c ≤ C) :
    cavityGaussianLinearMomentBound d p c M ≤ cavityGaussianLinearMomentBound d p C M := by
  have hi := cavity_standardGaussian_exp_norm_integrable d ((2 * p + 2 * c + 1) * Real.sqrt M)
  have hI := cavity_standardGaussian_exp_norm_integrable d ((2 * p + 2 * C + 1) * Real.sqrt M)
  have hpoint (z : EuclideanSpace ℝ (Fin d)) :
      Real.exp (((2 * p + 2 * c + 1) * Real.sqrt M) * ‖z‖) ≤
        Real.exp (((2 * p + 2 * C + 1) * Real.sqrt M) * ‖z‖) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg M)) (norm_nonneg z)
  exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (integral_mono hi hI hpoint)
    (integral_nonneg (fun _ => (Real.exp_pos _).le)) (Real.exp_pos _).le

end InvariantIsing

end

end OAI
