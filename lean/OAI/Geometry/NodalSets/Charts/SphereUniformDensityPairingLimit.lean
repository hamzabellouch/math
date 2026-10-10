import OAI.Geometry.NodalSets.Charts.SphereWeightedPairingLimit

namespace OAI

namespace Yau.Target
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
local instance sphereUniformDensityMeasurable : MeasurableSpace Base := borel Base
local instance sphereUniformDensityBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereWeightedPairing_uniform_density_limit
    (rho : ℕ → Base → ℝ) (rho₀ : Base → ℝ)
    (hr : ∀ j, Continuous (rho j)) (hr₀ : Continuous rho₀)
    (htr : TendstoUniformly rho rho₀ atTop)
    (w1 w2 : ℕ → Base → ℝ) (v1 v2 : Base → ℝ)
    (hw1 : ∀ j, Continuous (w1 j)) (hw2 : ∀ j, Continuous (w2 j))
    (hv1 : Continuous v1) (hv2 : Continuous v2)
    (hc1 : TendstoUniformly w1 v1 atTop) (hc2 : TendstoUniformly w2 v2 atTop) :
    Tendsto (fun j ↦ sphereWeightedPairing (rho j) (w1 j) (w2 j)) atTop
      (𝓝 (sphereWeightedPairing rho₀ v1 v2)) := by
  let := sphereReferenceMeasure_finite
  obtain ⟨R,hR,hbR⟩ := sphere_uniform_eventual_bound rho rho₀ hr₀ htr
  obtain ⟨B1,hB1,hb1⟩ := sphere_uniform_eventual_bound w1 v1 hv1 hc1
  obtain ⟨B2,hB2,hb2⟩ := sphere_uniform_eventual_bound w2 v2 hv2 hc2
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall (fun j ↦ (((hr j).mul (hw1 j)).mul (hw2 j)).aestronglyMeasurable)
  · refine ⟨R*B1*B2,?_⟩
    filter_upwards [hbR,hb1,hb2] with j hjR hj1 hj2
    exact Eventually.of_forall (fun x ↦ by
      rw [norm_mul,norm_mul]
      exact mul_le_mul (mul_le_mul (hjR x) (hj1 x) (norm_nonneg _) hR.le)
        (hj2 x) (norm_nonneg _) (mul_nonneg hR.le hB1.le))
  · exact Eventually.of_forall (fun x ↦
      ((htr.tendsto_at x).mul (hc1.tendsto_at x)).mul (hc2.tendsto_at x))

theorem sphere_uniform_limit_normalized
    (rho : ℕ → Base → ℝ) (rho₀ : Base → ℝ)
    (hr : ∀ j, Continuous (rho j)) (hr₀ : Continuous rho₀)
    (htr : TendstoUniformly rho rho₀ atTop)
    (w : ℕ → Base → ℝ) (v : Base → ℝ)
    (hw : ∀ j, Continuous (w j)) (hv : Continuous v)
    (hc : TendstoUniformly w v atTop)
    (hn : ∀ j, sphereWeightedPairing (rho j) (w j) (w j)=1) :
    sphereWeightedPairing rho₀ v v=1 ∧ v ≠ 0 := by
  have ht := sphereWeightedPairing_uniform_density_limit rho rho₀ hr hr₀ htr
    w w v v hw hw hv hv hc hc
  have he : sphereWeightedPairing rho₀ v v=1 := by
    simp only [hn] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  refine ⟨he,?_⟩
  intro hz
  simp only [hz,sphereWeightedPairing,Pi.zero_apply,mul_zero,integral_zero] at he
  norm_num at he

end
end Yau.Target

end OAI
