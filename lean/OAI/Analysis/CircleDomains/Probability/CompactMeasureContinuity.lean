import OAI.Analysis.CircleDomains.Topology.NestedCompactTestPlan
import OAI.Analysis.CircleDomains.Probability.CompactPlanTestDensity
import OAI.Analysis.CircleDomains.Sobolev.MeasurePlanWeakDuality

namespace OAI

/-! Continuity of pointwise modulus on decreasing compact measure families
avoiding zero. The limiting probability plan supplies the lower bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace CircleDomainRigidity

lemma compact_intersection_modulus_lower
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ]
    (T : ℕ → Set (FiniteMeasure Z)) (hT : ∀ n, IsCompact (T n))
    (hne : ∀ n, (T n).Nonempty) (hanti : Antitone T)
    (hz : (0 : FiniteMeasure Z) ∉ T 0) {c : ℝ≥0} (hc : 0 < c)
    (hm : ∀ n, (c : ℝ≥0∞) < measureFamilyModulus (T n) Z σ (fun v => v.val)) :
    (c : ℝ≥0∞) ≤ measureFamilyModulus (⋂ n, T n) Z σ (fun v => v.val) := by
  let : CompactSpace (T 0) := isCompact_iff_compactSpace.mp (hT 0)
  have hcr : (0 : ℝ) < c := hc
  have hsq : Real.sqrt (c : ℝ)^2 = c := Real.sq_sqrt c.coe_nonneg
  obtain ⟨P,hPs,hPt⟩ := exists_nested_compact_test_plan σ T hT hne hanti hz
    (Real.sqrt_pos.mpr hcr) (by simpa only [hsq,ENNReal.ofReal_coe_nnreal] using hm)
  obtain ⟨q,hq,hbar,he⟩ := compact_plan_density_of_test_bound σ (hT 0) P
    (Real.sqrt_pos.mpr hcr) hPt
  have he' : (∫⁻ z, q z^2 ∂σ) ≤ (c : ℝ≥0∞)⁻¹ := by
    convert he using 1
    rw [inv_pow,hsq,ENNReal.ofReal_inv_of_pos hcr,ENNReal.ofReal_coe_nnreal]
  apply measureFamilyModulus_lower_of_barycenter σ (fun v : (⋂ n, T n) => v.val) P _ hq hbar hc he'
  filter_upwards [hPs] with v hv
  exact ⟨⟨v.val,hv⟩,rfl⟩

end CircleDomainRigidity

end

end OAI
