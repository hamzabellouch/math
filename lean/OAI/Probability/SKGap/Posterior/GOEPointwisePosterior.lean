import Mathlib
import OAI.Probability.SKGap.Brownian.ContinuousKernel
import OAI.Probability.SKGap.Matrix.GOEResidualCov

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real GaussianDensity GaussianRegression
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def goeLaw (r : ℝ) : Measure ((ι × ι) → ℝ) :=
  (gaussianCoordinates (MatrixCoordinates ι)).map (fun g p => goeMatrix r g p.1 p.2)

def conditionalGoeLaw (r v : ℝ) (m z : ι → ℝ) : Measure ((ι × ι) → ℝ) :=
  ((gaussianCoordinates (MatrixCoordinates ι)).map (goeRegressionResidual r v m)).map
    (fun R => R+goeRegressionCoefficient r v m*ᵥz)

theorem goe_pointwise_posterior {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) (m z : ι → ℝ) :
    (goeLaw (ι := ι) r).withDensity (fun W => ENNReal.ofReal
      (radialDensity (sqrt v) (z-(fun i => ∑ k, W (i,k)*m k)))) =
    ENNReal.ofReal (rankOneDensity (r*(m⬝ᵥm)+v) r m z) • conditionalGoeLaw r v m z := by
  have hXY := goe_observation_joint_gaussian r v m
  let : IsProbabilityMeasure (goeLaw (ι := ι) r) :=
    inferInstanceAs (IsProbabilityMeasure ((gaussianCoordinates (MatrixCoordinates ι)).map _))
  let ρ := (gaussianCoordinates (MatrixCoordinates ι)).map (goeRegressionResidual r v m)
  have hreg := regression_joint_law hXY (goeRegressionCoefficient r v m) (goe_regression_covariance hr hv m)
  have hj := goe_joint_noise_law r v m
  rw [goe_noise_density hr hv] at hj
  rw [goe_observation_density hr hv m] at hreg
  have hjoint : ((goeLaw (ι := ι) r).prod ((volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (radialDensity (sqrt v) x)))).map
      (fun q => (q.1,(fun i => ∑ k, q.1 (i,k)*m k)+q.2)) =
    (ρ.prod ((volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (rankOneDensity (r*(m⬝ᵥm)+v) r m x)))).map
      (fun q => (q.1+goeRegressionCoefficient r v m*ᵥq.2,q.2)) := hj.trans hreg
  have hq : 0 ≤ m⬝ᵥm := Finset.sum_nonneg (fun i _ => mul_self_nonneg (m i))
  have hs := add_pos_of_nonneg_of_pos (mul_nonneg hr hq) hv
  exact continuous_kernel_posterior (goeLaw (ι := ι) r) ρ (continuous_radialDensity _)
    (continuous_rankOneDensity _ _ m) (fun x => (radialDensity_pos (sqrt_pos.mpr hv) x).le)
    (fun x => (rankOneDensity_pos hs hr m x).le) (by positivity)
    (radialDensity_le (sqrt_pos.mpr hv)) (by fun_prop) (by fun_prop) hjoint z

omit [Nonempty ι] in

theorem conditionalGoeLaw_block {r v c : ℝ} (hr : 0 ≤ r) (hv : 0 < v)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) (z : ι → ℝ) :
    conditionalGoeLaw r v (c • u) z =
      (gaussianCoordinates (MatrixCoordinates ι)).map (fun g p =>
        goeBlockResidual r (sqrt (v/(r*c^2+v))) (sqrt (v/(v+2*r*c^2))) u g p.1 p.2+
        (goeRegressionCoefficient r v (c • u)*ᵥz) p) := by
  rw [conditionalGoeLaw,goe_regression_residual_law hr hv hu,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (goeBlockResidual_gaussian r _ _ u).aemeasurable]
  rfl

theorem goe_pointwise_conditional_integral {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v)
    (m z : ι → ℝ) (f : ((ι × ι) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g, ENNReal.ofReal (radialDensity (sqrt v) (z-goeMatrix r g*ᵥm))*
      f (fun p => goeMatrix r g p.1 p.2) ∂gaussianCoordinates (MatrixCoordinates ι)) =
    ENNReal.ofReal (rankOneDensity (r*(m⬝ᵥm)+v) r m z)*
      (∫⁻ W, f W ∂conditionalGoeLaw r v m z) := by
  have hh := congrArg (fun ν => ∫⁻ W, f W ∂ν) (goe_pointwise_posterior hr hv m z)
  have hφ : Measurable (fun W : (ι × ι) → ℝ => ENNReal.ofReal (radialDensity (sqrt v) (z-(fun i => ∑ k, W (i,k)*m k)))) :=
    ((continuous_radialDensity _).comp (by fun_prop)).measurable.ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hφ hf,lintegral_smul_measure] at hh
  rw [goeLaw,lintegral_map (hφ.mul hf) (by unfold goeMatrix; fun_prop)] at hh
  exact hh

end SKGap
end
end

end OAI
