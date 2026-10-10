import Mathlib
import OAI.Probability.SKBarriers.Gaussian.FiberLipschitzLinear
import OAI.Probability.SKBarriers.Scalar.ScalarLocalTentMoments
import OAI.Probability.SKBarriers.Scalar.ScalarGradientComposition

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarLevelField_tent_peak (n : ℕ) (v : Fin n → ℝ) (l r s : Fin (n+1))
    (hlr : l ≤ r) (hrs : r ≤ s) {h B : ℝ} (hh : h≠0)
    (hleft : scalarPrefixVariance n v r-scalarPrefixVariance n v l=B*h) :
    scalarLevelField n v r (coordinateVector n (scalarTentVector n v l r s h))=B := by
  rw [scalarLevelField_tentVector,min_self,min_eq_right hlr,min_eq_left hrs]
  have he : 2*scalarPrefixVariance n v r-scalarPrefixVariance n v l-scalarPrefixVariance n v r=B*h := by linarith
  rw [he,mul_div_cancel_right₀ B hh]

theorem scalarPath_tent_mixed_error (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f F : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (hF : BoundedDerivs F) (hFs : ScalarSpinConvex F)
    (l r s : Fin (n+1)) (hlr : l ≤ r) (hrs : r ≤ s) {h B : ℝ} (hh : 0<h) (hB : 0 ≤ B)
    (hleft : scalarPrefixVariance n v r-scalarPrefixVariance n v l=B*h)
    (hright : scalarPrefixVariance n v s-scalarPrefixVariance n v r=B*h)
    {g : ℝ → ℝ} {M : ℝ≥0} (hg : LipschitzWith M g) (hb : ∀ y, |g y| ≤ 1) (x : ℝ) :
    |(∫ z, coordinateLinear n (scalarTentVector n v l r s h) z*
      rootGradient 0 F (scalarLevelField n v r z)*g (scalarSpinField n v z)
      ∂hierarchyPathLaw n m (fun z => f (scalarSpinField n v z)) x)-
      B*(∫ z, rootHessian 0 F (scalarLevelField n v r z)*g (scalarSpinField n v z)
        ∂hierarchyPathLaw n m (fun z => f (scalarSpinField n v z)) x)| ≤
      B*scalarTentAtomMass n m l s := by
  let V := hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z))
  have hV := hierarchyPathLogDensity_regular n m (hf.compCLM (scalarSpinField n v))
  have HF := scalarGradient_comp_regular hF hFs (scalarLevelField n v r)
  have H := fiberGaussian_linear_error_lipschitz n V _ hV HF.1 HF.2.1 HF.2.2
    (fun z => (hFs.bounds _).1) hg hb (scalarSpinField n v) x (scalarTentVector n v l r s h)
    (by
      rw [← scalarLevelField_last]
      exact (scalarTentVector_prefix_bounds n v l r s hlr hrs hh hB hleft hright _).2 (Or.inr (Fin.le_last s)))
    (B*scalarTentAtomMass n m l s)
    (fun z => (scalarLogDensity_tent_bounds n m v hm hmono hf hspin l r s hlr hrs hh hB hleft hright z).1)
  rw [hierarchyPathLaw_eq_tilted n m _ (hf.compCLM (scalarSpinField n v))]
  simp_rw [scalarGradient_comp_fderiv hF,smul_apply,smul_eq_mul,
    scalarLevelField_tent_peak n v l r s hlr hrs (ne_of_gt hh) hleft] at H
  have he : (fun z : ParameterSpace n => rootHessian 0 F (scalarLevelField n v r z)*B*g (scalarSpinField n v z))=
      fun z => B*(rootHessian 0 F (scalarLevelField n v r z)*g (scalarSpinField n v z)) := by funext z; ring
  rw [he,integral_const_mul] at H
  exact H

end SK.Analytic

end
end

end OAI
