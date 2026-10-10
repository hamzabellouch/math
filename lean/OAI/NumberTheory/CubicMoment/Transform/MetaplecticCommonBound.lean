import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCoefficientMajorant

namespace OAI

/-! The two complementary common-factor bounds in each retained
metaplectic block. Both come from actual divisibility. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticCommonNorm_le_level {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) : metaplecticCommonNorm r n ≤ norm r := by
  let S := (primaryPrimeFactors r).filter (fun p => p ∣ n.val)
  have hsub : S ⊆ primaryPrimeFactors r := Finset.filter_subset _ _
  have hdiv : (∏ p ∈ S, p) ∣ r := (primary_subsets_prod_dvd hr hsub r).mpr (by
    intro p hp
    exact (primaryPrimeFactor_spec hr (hsub hp)).2)
  have he : metaplecticCommonNorm r n = norm (∏ p ∈ S, p) := by
    rw [norm_finset_prod]
    rfl
  rw [he]
  exact norm_le_of_dvd (primary_ne_zero hr) hdiv

lemma metaplecticCommonNorm_nonneg (r : Eisenstein) (n : MetaplecticDualArgument) :
    0 ≤ metaplecticCommonNorm r n := by
  unfold metaplecticCommonNorm
  exact Finset.prod_nonneg (fun p _ => norm_nonneg p)

lemma metaplecticCommonNorm_le_geometric {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) (k : ℕ) (ζ : Eisensteinˣ)
    {h h' w : Eisenstein} (hh : primary h) (hh' : primary h') (hwr : IsCoprime w r)
    (he : n.val = lambdaE^k*ζ.val*h*w*h'^3) :
    metaplecticCommonNorm r n ≤ Real.sqrt (norm r*(norm h*norm h')) := by
  have hR := metaplecticCommonNorm_le_level hr n
  have hH := metaplecticCommonNorm_le_supported hr n k ζ hh hh' hwr he
  have hg := metaplecticCommonNorm_nonneg r n
  have hprod : metaplecticCommonNorm r n^2 ≤ norm r*(norm h*norm h') := by
    simpa only [pow_two] using mul_le_mul hR hH hg (norm_nonneg r)
  exact Real.le_sqrt_of_sq_le hprod

lemma metaplectic_actual_coefficient_common_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} {C : ℝ} (hC : 0 ≤ C)
    {r : Eisenstein} (hr : primary r) (n : MetaplecticDualArgument)
    {j : ℤ} {h' : Eisenstein} (ha : ‖a r n‖ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')) :
    ‖a r n*metaplecticLocalCoefficient r n‖ ≤
      C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')*metaplecticCommonNorm r n := by
  rw [norm_mul]
  exact mul_le_mul ha (norm_metaplecticLocalCoefficient_le hr n)
    (_root_.norm_nonneg _) (by positivity)

end CubicFirstMoment

end

end OAI
