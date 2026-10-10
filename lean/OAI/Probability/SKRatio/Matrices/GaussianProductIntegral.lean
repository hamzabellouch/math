import Mathlib
import OAI.Probability.SKRatio.Matrices.PowExponentialPair

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Real
open scoped Topology
section ProductMoments
variable {κ : Type*} [Fintype κ]

lemma gaussianProduct_integral (F : EuclideanSpace ℝ κ → ℝ) (hF : Continuous F) :
    (∫ g : κ → ℝ, F (WithLp.toLp 2 g) ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ x, F x ∂stdGaussian (EuclideanSpace ℝ κ) := by
  rw [← map_pi_eq_stdGaussian]
  exact (integral_map (by fun_prop) hF.aestronglyMeasurable).symm

lemma gaussianProduct_integrable_lipschitz {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) :
    Integrable (fun g : κ → ℝ => F (WithLp.toLp 2 g))
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  have hi := gaussian_integrable_lipschitz (μ := stdGaussian (EuclideanSpace ℝ κ)) hF
  rw [← map_pi_eq_stdGaussian] at hi
  exact hi.comp_measurable (by fun_prop)

lemma gaussianProduct_abs_centered_moment {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) (hL : 0 < L) (k : ℕ) :
    (∫ g : κ → ℝ, |F (WithLp.toLp 2 g)-
      ∫ h : κ → ℝ, F (WithLp.toLp 2 h) ∂Measure.pi (fun _ => gaussianReal 0 1)|^k
        ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      (2*(k.factorial : ℝ)*exp (π^2/8))*(L:ℝ)^k := by
  rw [gaussianProduct_integral F hF.continuous]
  rw [gaussianProduct_integral (fun x => |F x-∫ y, F y ∂stdGaussian _|^k) ((hF.continuous.sub continuous_const).abs.pow k)]
  exact stdGaussian_abs_centered_moment hF hL k

lemma gaussianProduct_centered_L1 {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) (hL : 0 < L) :
    (∫ g : κ → ℝ, |F (WithLp.toLp 2 g)-
      ∫ h : κ → ℝ, F (WithLp.toLp 2 h) ∂Measure.pi (fun _ => gaussianReal 0 1)|
        ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      (2*exp (π^2/8))*(L:ℝ) := by
  simpa using gaussianProduct_abs_centered_moment hF hL 1

end ProductMoments
end SKRatioGaussian

open MeasureTheory
noncomputable section

end
end
end
end
end
end
end

end OAI
