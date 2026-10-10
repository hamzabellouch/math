import OAI.Geometry.RCD.Metric.CanonicalBallMassLower
import OAI.Geometry.RCD.Sobolev.CompactRestrictedLaw
import OAI.Geometry.RCD.Heat.CompactHeatFactors
import OAI.Geometry.RCD.Heat.SmallNoiseLogBounds

namespace OAI

/-! # Actual reference normalization for a uniform compact endpoint law

If the reference point lies in an interior ball of the support, its heat
factor with constant endpoint weight stays between two fixed positive
constants at small times. Hence its scaled logarithm tends to zero.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_reference_mass {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (hν : ν.map Subtype.val = uniformOn (hausdorff n X) S)
    (z : X) {r : ℝ} (hr : 0 < r) (hball : ball z r ⊆ S) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 → t ≤ r^2 →
      c ≤ hX.compactHeatFactor hn p ν 1 t ht z ∧
      hX.compactHeatFactor hn p ν 1 t ht z ≤ C := by
  let μ := hausdorff n X
  have hS : IsCompact S := isCompact_iff_compactSpace.mpr inferInstance
  have hSf : μ S ≠ ∞ := (hX.finiteOnBounded S hS.isBounded).ne
  have hS0 : μ S ≠ 0 := ne_of_gt ((hX.fullSupport z r hr).trans_le (measure_mono hball))
  have hV : 0 < μ.real S := ENNReal.toReal_pos hS0 hSf
  obtain ⟨b,hb,hmass⟩ := hX.canonicalHeatKernel_ball_mass_lower hn p
  refine ⟨b/(μ.real S),(μ.real S)⁻¹,div_pos hb hV,inv_pos.mpr hV,?_⟩
  intro t ht ht1 htr
  have hi := hX.canonicalHeatKernel_integrable hn p t ht z
  have hm : Measurable (hX.canonicalHeatKernel hn p t z) :=
    (hX.canonicalHeatKernel_continuous_joint hn p t ht).comp
      (continuous_const.prodMk continuous_id) |>.measurable
  have he : hX.compactHeatFactor hn p ν 1 t ht z =
      (μ.real S)⁻¹*(∫ x in S, hX.canonicalHeatKernel hn p t z x ∂μ) := by
    change (∫ a : S, hX.canonicalHeatKernel hn p t z a*1 ∂ν) = _
    simp only [mul_one]
    exact restricted_law_integral μ ν hν _ hm
  have hl : b ≤ ∫ x in S, hX.canonicalHeatKernel hn p t z x ∂μ :=
    (hmass z r t hr ht ht1 htr).trans (setIntegral_mono_set hi.integrableOn
      (Eventually.of_forall fun x => hX.canonicalHeatKernel_nonneg hn p t z x)
      (Eventually.of_forall hball))
  have hu : (∫ x in S, hX.canonicalHeatKernel hn p t z x ∂μ) ≤ 1 := by
    rw [← hX.canonicalHeatKernel_mass_one hn p t ht z]
    exact setIntegral_le_integral hi
      (Eventually.of_forall fun x => hX.canonicalHeatKernel_nonneg hn p t z x)
  rw [he]
  constructor
  · simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hV.le)
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hV.le)

theorem compact_heat_reference_scaled_log {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (hν : ν.map Subtype.val = uniformOn (hausdorff n X) S)
    (z : X) {r : ℝ} (hr : 0 < r) (hball : ball z r ⊆ S)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun k => ε k*Real.log
      (hX.compactHeatFactor hn p ν 1 (ε k*a) (mul_pos (hε k) ha) z)) atTop (𝓝 0) := by
  obtain ⟨c,C,hc,_hC,hbound⟩ := hX.compact_heat_reference_mass hn p ν hν z hr hball
  have ht : Tendsto (fun k => ε k*a) atTop (𝓝 0) := by
    simpa only [zero_mul] using hε0.mul_const a
  apply small_noise_log_tendsto_zero (fun k => (hε k).le) hε0 hc
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    ht.eventually (gt_mem_nhds (sq_pos_of_pos hr))] with k hk hk'
  exact hbound (ε k*a) (mul_pos (hε k) ha) hk.le hk'.le

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
