import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeWedgeMassLower

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricNormalCharts Filter
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ConnectedSpace X] [SecondCountableTopology X]
attribute [local instance] unitMeasurable unitBorel unitT2

theorem separating_current_L2_correction
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) (hc : IsClosed α)
    (A : FiniteCharts X)
    (E : ∀ p : A.centers, ParametrixData J α ht p.val)
    (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
    (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
    (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ Q : L2 A J α hs ht true,
      l2AntiProjection A J α hs ht Q = Q ∧
      l2Star A J α hs ht Q = Q ∧
      (∀ a : smoothForms X 2, IsClosed a.val →
        unitMeasureCurrent J (hermitianMetric J α hs ht) μ a+
          ⟪Q,smoothL2 A J α hs ht true a⟫ = 0) ∧
      ⟪Q,smoothL2 A J α hs ht true ⟨α,hs⟩⟫ = -1 := by
  obtain ⟨B,hBc,hBR,L₀,hL₀,hB⟩ := exists_convergent_closed_lift A J α hs ht D hD (hermitianMetric J α hs ht)
  obtain ⟨C,K,hC,hK,hcross⟩ := separating_current_mass_and_cross A J α hs ht E hE D hD μ hann
  obtain ⟨L,hL,hlower⟩ := separating_current_wedge_lower A J α hs ht E hE D hD μ hann
  have hbound : ∀ᶠ r in 𝓝[>] (0:ℝ),
      ‖hodgeCorrectionFamily A J α hs ht D hD B (hermitianMetric J α hs ht) μ r‖ ≤
        K+Real.sqrt (K^2+L) := by
    have hsmall : ∀ᶠ r in 𝓝[>] (0:ℝ), r < 1 :=
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0) (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin,hsmall] with r hr hr1
    change 0 < r at hr
    have hrep := ((hB μ).1 r hr hr1.le).1
    let S := hodgeSmoothingCover A J α hs ht D hD r hr
    have hcr := (hcross r hr hr1.le S).2
      (hodgeCorrectionRegularize A J α hs ht D hD B (hermitianMetric J α hs ht) μ r hr) (by
        intro a
        rw [hrep,map_sub,hodgeCorrectionSource_anti,sub_self])
    have he := hodgeCorrected_energy_identity A J α hs ht D hD B hBc hBR
      (hermitianMetric J α hs ht) μ hann r hr S hrep
    simpa only [hodgeCorrectionFamily,dite_eq_left hr] using
      norm_bound_of_wedge_energy (S.regularize (hermitianMetric J α hs ht) μ)
        (hodgeCorrectionRegularize A J α hs ht D hD B (hermitianMetric J α hs ht) μ r hr)
        _ L K hL (hlower r hr S) hcr he
  obtain ⟨Q,hQ⟩ := weak_limit_functional_represented
    (hodgeCorrectionSource A J α hs ht B (hermitianMetric J α hs ht) μ)
    (hodgeCorrectionFamily A J α hs ht D hD B (hermitianMetric J α hs ht) μ)
    (K+Real.sqrt (K^2+L)) hbound ((hB μ).2)
  have hQa : l2AntiProjection A J α hs ht Q = Q := by
    apply ext_inner_right ℝ
    intro b
    refine (smoothL2_dense A J α hs ht true).induction_on b
      (isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)) ?_
    intro a
    rw [l2AntiProjection_self_adjoint,← preAntiProjection_smooth]
    exact (hQ (preAntiProjection A J α hs ht a)).trans
      ((hodgeCorrectionSource_anti A J α hs ht B (hermitianMetric J α hs ht) μ a).trans (hQ a).symm)
  refine ⟨Q,hQa,?_,?_,?_⟩
  · rw [← hQa,l2AntiProjectionStar]
  · intro a ha
    rw [show ⟪Q,smoothL2 A J α hs ht true a⟫ =
      hodgeCorrectionSource A J α hs ht B (hermitianMetric J α hs ht) μ a from hQ a]
    exact hodgeCorrectionSource_closed A J α hs ht B hBc hBR
      (hermitianMetric J α hs ht) μ hann a ha
  · exact (hQ ⟨α,hs⟩).trans (hodgeCorrectionSource_taming A J α hs ht B hBc hBR μ hann hc)

end TamingCompatibility.GeometricHilbert

end
end

end OAI
