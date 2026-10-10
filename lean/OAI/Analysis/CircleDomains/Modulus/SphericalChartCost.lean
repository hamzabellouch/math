import OAI.Analysis.CircleDomains.Probability.SphericalSliceDensity
import OAI.Analysis.CircleDomains.Modulus.WeightedPhysicalChart

namespace OAI

/-! Square-integrable planar derivatives give the finite spherical
weights used by each local tag payment measure. The inverse chart is
Borel, including its arbitrary value at infinity. -/

open Set Function MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem measurable_finiteCoord : Measurable finiteCoord := by
  classical
  obtain ⟨j, hj, he⟩ := OnePoint.isOpenEmbedding_coe.measurableEmbedding.exists_measurable_extend
    (measurable_id (α := ℂ)) (fun _ => inferInstance)
  have hfun : ({OnePoint.infty} : Set Sphere).piecewise (fun _ => (0 : ℂ)) j = finiteCoord := by
    funext p
    cases p using OnePoint.rec with
    | infty => simp [finiteCoord]
    | coe z =>
      simpa only [mem_singleton_iff, OnePoint.coe_ne_infty, not_false_eq_true, piecewise_eq_of_notMem,
        finiteCoord_coe, comp_apply, id_eq] using congrFun he z
  rw [← hfun]
  exact measurable_const.piecewise (measurableSet_singleton _) hj

def localizedSphericalChartWeight (L : ℝ≥0) (A : Set ℂ) (k : ℂ → ℝ≥0∞) : Sphere → ℝ≥0∞ :=
  fun y => (L : ℝ≥0∞) * (((↑) : ℂ → Sphere) '' A).indicator (fun y => k (finiteCoord y)) y

theorem measurable_localizedSphericalChartWeight (L : ℝ≥0) {A : Set ℂ}
    (hA : MeasurableSet A) {k : ℂ → ℝ≥0∞} (hk : Measurable k) :
    Measurable (localizedSphericalChartWeight L A k) :=
  measurable_const.mul ((hk.comp measurable_finiteCoord).indicator
    (OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hA))

theorem localizedSphericalChartWeight_coe (L : ℝ≥0) (A : Set ℂ) (k : ℂ → ℝ≥0∞) (z : ℂ) :
    localizedSphericalChartWeight L A k (z : Sphere) = (L : ℝ≥0∞) * A.indicator k z := by
  classical
  by_cases hz : z ∈ A <;> simp [localizedSphericalChartWeight, hz]

theorem localizedSphericalChartWeight_square_finite (L : ℝ≥0) {A : Set ℂ}
    (hA : MeasurableSet A) {k : ℂ → ℝ≥0∞} (hk : Measurable k)
    (henergy : (∫⁻ z in A, k z ^ 2) < ∞) :
    (∫⁻ y, localizedSphericalChartWeight L A k y ^ 2 ∂sphericalArea) < ∞ := by
  rw [lintegral_sphericalArea _ ((measurable_localizedSphericalChartWeight L hA hk).pow_const 2)]
  simp_rw [localizedSphericalChartWeight_coe]
  have hb : (∫⁻ z, ENNReal.ofReal (sphericalAreaDensity z) * ((L : ℝ≥0∞) * A.indicator k z) ^ 2) ≤
      (4 : ℝ≥0∞) * (L : ℝ≥0∞) ^ 2 * ∫⁻ z in A, k z ^ 2 := by
    calc
      _ ≤ ∫⁻ z, ((4 : ℝ≥0∞) * (L : ℝ≥0∞) ^ 2) * A.indicator (fun z => k z ^ 2) z := by
        apply lintegral_mono
        intro z
        by_cases hz : z ∈ A
        · simp only [indicator_of_mem hz, mul_pow]
          have hD : ENNReal.ofReal (sphericalAreaDensity z) ≤ 4 :=
            (ENNReal.ofReal_le_ofReal (sphericalAreaDensity_le_four z)).trans_eq (by norm_num)
          simpa only [mul_assoc] using mul_le_mul' hD (le_refl ((L : ℝ≥0∞) ^ 2 * k z ^ 2))
        · simp only [indicator_of_notMem hz, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
          exact le_rfl
      _ = _ := by rw [lintegral_const_mul' _ _ (by finiteness), lintegral_indicator hA]
  exact hb.trans_lt (ENNReal.mul_lt_top (by finiteness) henergy)

end CircleDomainRigidity

end

end OAI
