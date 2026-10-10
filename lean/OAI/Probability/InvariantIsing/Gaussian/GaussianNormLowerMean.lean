import OAI.Probability.InvariantIsing.Gaussian.GaussianCoordinateNorm

namespace OAI

/-! The matching lower mean bound for a finite-dimensional Gaussian norm. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma gaussianNorm_sq_integral {ι : Type*} [Fintype ι] :
    (∫ z : EuclideanSpace ℝ ι, ‖z‖^2 ∂stdGaussian _) = Fintype.card ι := by
  have hZ : HasLaw (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)
      (stdGaussian _) (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).measurable.aemeasurable,map_pi_eq_stdGaussian⟩
  rw [← hZ.integral_comp (f := fun z => ‖z‖^2) (by fun_prop)]
  exact gaussianCoordinateVector_sq_integral (id : ι → ι)

lemma gaussianNorm_lower_mean {ι : Type*} [Fintype ι] :
    Real.sqrt ((Fintype.card ι : ℝ)-1) ≤ ∫ z : EuclideanSpace ℝ ι, ‖z‖ ∂stdGaussian _ := by
  have hL : LipschitzWith 1 (norm : EuclideanSpace ℝ ι → ℝ) := lipschitzWith_one_norm
  have hv := finiteGaussian_lipschitz_variance hL
  rw [variance_eq_sub (finiteGaussian_lipschitz_memLp_two hL)] at hv
  change (∫ z : EuclideanSpace ℝ ι, ‖z‖^2 ∂stdGaussian _) - _ ≤ (1 : ℝ)^2 at hv
  rw [gaussianNorm_sq_integral] at hv
  have hn : 0 ≤ ∫ z : EuclideanSpace ℝ ι, ‖z‖ ∂stdGaussian _ := integral_nonneg (fun z => norm_nonneg z)
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact hn
  · nlinarith

end InvariantIsing

end

end OAI
