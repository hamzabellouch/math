import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.UniformConvergence
import OAI.Geometry.NodalSets.Charts.SphereReferenceMeasurePositive

namespace OAI

namespace Yau.Target
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
local instance sphereWeightedPairingLimitMeasurable : MeasurableSpace Base := borel Base
local instance sphereWeightedPairingLimitBorel : BorelSpace Base := ⟨rfl⟩

lemma sphere_uniform_eventual_bound (w : ℕ → Base → ℝ) (v : Base → ℝ)
    (hv : Continuous v) (ht : TendstoUniformly w v atTop) :
    ∃ B > 0, ∀ᶠ j in atTop, ∀ x, |w j x| ≤ B := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  refine ⟨max 0 C+1,by positivity,?_⟩
  filter_upwards [Metric.tendstoUniformly_iff.mp ht 1 (by norm_num)] with j hj x
  have hb : |v x| ≤ max 0 C := by
    have hb' : |v x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x (mem_univ x)
    exact hb'.trans (le_max_right _ _)
  have hd : |v x-w j x| < 1 := by simpa only [Real.dist_eq] using hj x
  have hvb := abs_le.mp hb
  have hdb := abs_lt.mp hd
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem sphereWeightedPairing_family_limit {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (rho : T → Base → ℝ) (hr : Continuous (fun z : T × Base ↦ rho z.1 z.2))
    (t : ℕ → T) (t0 : T) (ht : Tendsto t atTop (𝓝 t0))
    (w1 w2 : ℕ → Base → ℝ) (v1 v2 : Base → ℝ)
    (hw1 : ∀ j, Continuous (w1 j)) (hw2 : ∀ j, Continuous (w2 j))
    (hv1 : Continuous v1) (hv2 : Continuous v2)
    (hc1 : TendstoUniformly w1 v1 atTop) (hc2 : TendstoUniformly w2 v2 atTop) :
    Tendsto (fun j ↦ sphereWeightedPairing (rho (t j)) (w1 j) (w2 j)) atTop
      (𝓝 (sphereWeightedPairing (rho t0) v1 v2)) := by
  let := sphereReferenceMeasure_finite
  obtain ⟨R,hR⟩ := (isCompact_univ : IsCompact (univ : Set (T × Base))).exists_bound_of_continuousOn
    hr.continuousOn
  obtain ⟨B1,hB1,hb1⟩ := sphere_uniform_eventual_bound w1 v1 hv1 hc1
  obtain ⟨B2,hB2,hb2⟩ := sphere_uniform_eventual_bound w2 v2 hv2 hc2
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall (fun j ↦
      (((hr.comp (continuous_const.prodMk continuous_id)).mul (hw1 j)).mul (hw2 j)).aestronglyMeasurable)
  · refine ⟨(max 0 R)*B1*B2,?_⟩
    filter_upwards [hb1,hb2] with j hj1 hj2
    exact Eventually.of_forall (fun x ↦ by
      rw [norm_mul,norm_mul]
      have hb : ‖rho (t j) x‖ ≤ max 0 R := (hR (t j,x) (mem_univ _)).trans (le_max_right _ _)
      exact mul_le_mul (mul_le_mul hb (hj1 x) (norm_nonneg _) (le_max_left _ _))
        (hj2 x) (norm_nonneg _) (mul_nonneg (le_max_left _ _) hB1.le))
  · exact Eventually.of_forall (fun x ↦
      (((hr.tendsto (t0,x)).comp (ht.prodMk_nhds tendsto_const_nhds)).mul (hc1.tendsto_at x)).mul
        (hc2.tendsto_at x))

end
end Yau.Target

end OAI
