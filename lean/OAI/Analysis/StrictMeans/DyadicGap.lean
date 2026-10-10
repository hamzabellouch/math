import OAI.Analysis.StrictMeans.EqualityBarrier

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

theorem dyadicExponent_lt_quarter : dyadicExponent < 1/4 := by
  by_contra hn
  have hβ : 1/4 ≤ dyadicExponent := le_of_not_gt hn
  have hβ0 : 0 ≤ dyadicExponent := dyadicExponent_nonneg
  obtain ⟨μ,hμ⟩ := exists_exact_affine_probability_continuous (by linarith : 0 < dyadicExponent)
  have hlaw : AffineProbabilityLaw μ dyadicExponent := by
    intro z φ hφ
    rw [← weightedRebaseMeasure_lintegral _ _ _ hφ,
      weightedRebaseMeasure_eq_smul μ dyadicExponent hμ z,lintegral_smul_measure]
    rfl
  let k := (dyadicExponent+2)/3
  have hk : k ≠ 0 := by dsimp [k]; linarith
  have hm := expected_normalizedJacobian_at_source_k μ dyadicExponent hβ
    (affine_real_law_mean_law μ dyadicExponent hμ)
  change k^2 * (∫ f, normalizedJacobian k (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) =
    ((4 * dyadicExponent - 1) * (dyadicExponent + 2)) / 9 at hm
  simp_rw [halfPlaneFunction_normalizedJacobian_I _ hk] at hm
  have ht := strict_weighted_transport μ dyadicExponent hβ0 hlaw
  have he : dyadicExponent = 1/4 := by
    have hle : k^2 * (∫ f, jacobianExpression k (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) ht.1
    rw [hm] at hle
    nlinarith
  have k_eq : (dyadicExponent+2)/3 = (3/4:ℝ) := by rw [he]; norm_num
  have hz : (∫ f, jacobianExpression ((dyadicExponent+2)/3) (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) = 0 := by
    dsimp [k] at hm
    rw [he] at hm ⊢
    norm_num at hm ⊢
    linarith
  have hae := ht.2 hz
  rw [k_eq] at hae
  exact affine_law_not_ae_zero_jacobian μ dyadicExponent hμ hae

end
end StrictInverseFirstPower

end

end OAI
