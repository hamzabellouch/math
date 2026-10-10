import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarLocalDensity
import OAI.Probability.SKBarriers.Scalar.ScalarTentGeometry
import OAI.Probability.SKBarriers.Gaussian.FiberLipschitzTent

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarTentAtomMass (n : ℕ) (m : Fin n → ℝ) (l s : Fin (n+1)) : ℝ :=
  ∑ j∈Finset.univ.filter (fun j : Fin (n+1) => l < j ∧ j < s), hierarchyAtom n m 1 j

theorem scalarLogDensity_tent_bounds (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (l r s : Fin (n+1)) (hlr : l ≤ r) (hrs : r ≤ s) {h B : ℝ} (hh : 0 < h) (hB : 0 ≤ B)
    (hleft : scalarPrefixVariance n v r-scalarPrefixVariance n v l=B*h)
    (hright : scalarPrefixVariance n v s-scalarPrefixVariance n v r=B*h) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z))) z
      (coordinateVector n (scalarTentVector n v l r s h))| ≤ B*scalarTentAtomMass n m l s ∧
    |fderiv ℝ (fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z)))) z
      (coordinateVector n (scalarTentVector n v l r s h)) (coordinateVector n (scalarTentVector n v l r s h))| ≤
      B^2*scalarTentAtomMass n m l s := by
  have HT (j) := scalarTentVector_prefix_bounds n v l r s hlr hrs hh hB hleft hright j
  apply scalarLogDensity_local_bound n m v hm hmono hf hspin _ _
    (Finset.univ.filter (fun j : Fin (n+1) => l < j ∧ j < s)) hB
  · intro j hj
    apply (HT j).2
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,not_and_or,not_lt] at hj
    exact hj
  · intro j _
    rw [abs_of_nonneg (HT j).1.1]
    exact (HT j).1.2
  · rw [← scalarLevelField_last]
    exact (HT _).2 (Or.inr (Fin.le_last s))

theorem scalarPath_tent_square_error (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (l r s : Fin (n+1)) (hlr : l ≤ r) (hrs : r ≤ s) {h B : ℝ} (hh : 0 < h) (hB : 0 ≤ B)
    (hleft : scalarPrefixVariance n v r-scalarPrefixVariance n v l=B*h)
    (hright : scalarPrefixVariance n v s-scalarPrefixVariance n v r=B*h)
    {g : ℝ → ℝ} {M : ℝ≥0} (hg : LipschitzWith M g) (hb : ∀ y, |g y| ≤ 1) (x : ℝ) :
    |(∫ z, (coordinateLinear n (scalarTentVector n v l r s h) z)^2*g (scalarSpinField n v z)
      ∂hierarchyPathLaw n m (fun z => f (scalarSpinField n v z)) x)-
      (∑ i, (scalarTentVector n v l r s h i)^2)*(∫ z, g (scalarSpinField n v z)
        ∂hierarchyPathLaw n m (fun z => f (scalarSpinField n v z)) x)| ≤
      (B*scalarTentAtomMass n m l s)^2+B^2*scalarTentAtomMass n m l s := by
  rw [hierarchyPathLaw_eq_tilted n m _ (hf.compCLM (scalarSpinField n v))]
  apply fiberGaussian_tent_error_lipschitz n _
    (hierarchyPathLogDensity_regular n m (hf.compCLM (scalarSpinField n v))) hg hb
    (scalarSpinField n v) x _ _ (B*scalarTentAtomMass n m l s) (B^2*scalarTentAtomMass n m l s)
  · intro z
    exact (scalarLogDensity_tent_bounds n m v hm hmono hf hspin l r s hlr hrs hh hB hleft hright z).1
  · intro z
    exact (scalarLogDensity_tent_bounds n m v hm hmono hf hspin l r s hlr hrs hh hB hleft hright z).2
  · rw [← scalarLevelField_last]
    exact (scalarTentVector_prefix_bounds n v l r s hlr hrs hh hB hleft hright _).2 (Or.inr (Fin.le_last s))

end SK.Analytic

end
end

end OAI
