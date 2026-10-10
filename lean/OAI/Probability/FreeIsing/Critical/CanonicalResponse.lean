import OAI.Probability.FreeIsing.Trees.InfiniteCanonicalPathResponse
import OAI.Probability.FreeIsing.Trees.InfiniteConeCavity
import OAI.Probability.FreeIsing.Trees.SelectedPathAttenuation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators

namespace Problem367

open PlantedSymmetry CavityFieldLimit PathSideBranches

theorem HasFreeIsingLaw.rootResponseProduct_eq_forward_product
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β)
    (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      rootResponseProduct hβ v (observation t p) =
      Real.tanh β ^ v.1.length * ∏ k ∈ Finset.range v.1.length,
        responseAttenuation (Real.tanh β) (forwardGaussianField μ t v k p) := by
  have hfield (i : Fin v.1.length) :=
    hμ.infiniteCavityField_path_eq_forward_posterior hβ t v i i.2
  filter_upwards [ae_all_iff.mpr hfield] with p hp
  unfold rootResponseProduct
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  exact congrArg (responseAttenuation (Real.tanh β)) (hp ⟨k, Finset.mem_range.mp hk⟩)

theorem HasFreeIsingLaw.integral_rootResponseProduct_sq_le_critical
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh β ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (v : TreeVertex d) :
    (∫ p, rootResponseProduct hβ v (observation t p) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh β ^ v.1.length) ^ 2 *
        Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh β) *
          min (Real.sqrt (t : ℝ)) 1) * (v.1.length : ℝ)) := by
  calc
    _ = (Real.tanh β ^ v.1.length) ^ 2 *
        ∫ p, ∏ k ∈ Finset.range v.1.length,
          responseAttenuation (Real.tanh β) (forwardGaussianField μ t v k p) ^ 2
          ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hμ.rootResponseProduct_eq_forward_product hβ t v] with p hp
      rw [hp, mul_pow, Finset.prod_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_forwardGaussianField_attenuation_le_exp_critical hμ hβ hd hcritical ht v)
      (sq_nonneg _)

theorem HasFreeIsingLaw.integral_gaussianRootResponse_sq_le_critical
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh β ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (v : TreeVertex d) :
    (∫ p, gaussianPosteriorResponse μ t (ConnectedHull.root d) v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh β ^ v.1.length) ^ 2 *
        Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh β) *
          min (Real.sqrt (t : ℝ)) 1) * (v.1.length : ℝ)) := by
  have he := integral_congr_ae ((hμ.gaussian_rootResponse_eq_canonical_product hβ t v).fun_comp
    (fun z : ℝ => z ^ 2))
  simp only [Function.comp_apply] at he
  rw [he]
  exact hμ.integral_rootResponseProduct_sq_le_critical hβ hd hcritical ht v

theorem HasFreeIsingLaw.integral_infiniteGibbsRootResponse_sq_le_critical
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh β ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (v : TreeVertex d) :
    (∫ p, infiniteGibbsResponse β (ConnectedHull.root d) v (observation t p) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh β ^ v.1.length) ^ 2 *
        Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh β) *
          min (Real.sqrt (t : ℝ)) 1) * (v.1.length : ℝ)) := by
  have he := integral_congr_ae ((hμ.infiniteGibbsRootResponse_eq_canonical_product hβ t v).fun_comp
    (fun z : ℝ => z ^ 2))
  simp only [Function.comp_apply] at he
  rw [he]
  exact hμ.integral_rootResponseProduct_sq_le_critical hβ hd hcritical ht v

end Problem367

end

end OAI
