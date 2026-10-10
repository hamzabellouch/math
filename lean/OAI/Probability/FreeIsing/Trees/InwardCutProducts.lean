import OAI.Probability.FreeIsing.Trees.FinitePathCutCost
import OAI.Probability.FreeIsing.Trees.InwardCutCost

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal
namespace Problem367.PathSideBranches

theorem inward_attenuation_prod_le_cut {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) (k n : ℕ) (hkn : k + n ≤ v.1.length) :
    ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      (∏ i ∈ Finset.range n, responseAttenuation (Real.tanh beta)
        (inwardGaussianField μ t v (k + i) z) ^ 2) ≤
      Real.exp (4 * beta / (1 - Real.tanh beta)) *
        (∏ i ∈ Finset.range n, responseAttenuation (Real.tanh beta)
          (cutInwardGaussianField μ t v k (k + i) z) ^ 2) := by
  have hq0 : 0 ≤ Real.tanh beta := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta) (Real.cosh_pos beta).le
  have hq1 := Real.tanh_lt_one beta
  have htheta : Real.tanh beta ^ 2 ≤ 1 := by
    nlinarith [mul_self_le_mul_self hq0 hq1.le]
  by_cases hn : n = 0
  · subst n
    filter_upwards [] with z
    simpa only [Finset.range_zero, Finset.prod_empty, mul_one] using
      Real.one_le_exp (show 0 ≤ 4 * beta / (1 - Real.tanh beta) by positivity)
  · have hk : k < v.1.length := by omega
    have hz := inward_cut_difference_initial_sharp hμ hbeta t v hk
    have hs : ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
        ∀ i : ℕ, i + 1 < n →
          |inwardGaussianField μ t v (k + i + 1) z -
            cutInwardGaussianField μ t v k (k + i + 1) z| ≤
          Real.tanh beta * |inwardGaussianField μ t v (k + i) z -
            cutInwardGaussianField μ t v k (k + i) z| := by
      apply ae_all_iff.mpr
      intro i
      by_cases hi : i + 1 < n
      · filter_upwards [inward_cut_difference_step hμ hbeta t v
          (k := k) (i := k + i) (by omega) (by omega)] with z h
        exact fun _ => h
      · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
    filter_upwards [hz, hs] with z hzero hstep
    apply PathCutCost.attenuation_prod_le_exp_mul_of_finite_contraction n
      htheta hq0 hq1
    · simpa only [Nat.add_zero] using hzero
    · intro i hi
      simpa only [Nat.add_assoc] using hstep i hi

end Problem367.PathSideBranches

end

end OAI
