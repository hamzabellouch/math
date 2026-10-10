import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeMassBound

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

include hE D hD in
lemma separating_current_mass_and_cross
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
        ‖S.regularize (hermitianMetric J α hs ht) μ‖^2 ≤ C/r^2 ∧
        ∀ V : L2 A J α hs ht true,
          (∀ a : PreL2 A J α hs ht true,
            ⟪V,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
              (a-preAntiProjection A J α hs ht a))⟫ = 0) →
          |⟪S.regularize (hermitianMetric J α hs ht) μ,V⟫| ≤ K*‖V‖ := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨M,hM,hgrowth⟩ := separating_probability_quadratic_growth J α hs ht μ hann
  have hg : ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {v | ENNReal.ofReal (dist x v.val.proj) < ENNReal.ofReal s} ≤ M*s^2 := by
    intro x s hs'
    simpa only [← edist_dist,geometric_edist_eq J α hs ht] using hgrowth x s hs'
  obtain ⟨C,B,hC,hB,hm⟩ :=
    same_resolvent_current_mass_bound A J α hs ht E hE D hD (hermitianMetric J α hs ht)
  obtain ⟨K,hK,hk⟩ :=
    same_resolvent_current_mass_cross A J α hs ht E hE D hD (hermitianMetric J α hs ht)
      μ M hM hg
  exact ⟨C*M+B,K,add_nonneg (mul_nonneg hC hM) hB,hK,
    fun r hr hr1 S => ⟨hm μ M hM hg r hr hr1 S,hk r hr hr1 S⟩⟩

include hE D hD in

theorem exists_counterexample_mass_cross
    (hn : ¬ ∃ η : TwoForm X, IsSymplectic η ∧ Compatible η J) :
    ∃ μ : Measure (MetricUnit (hermitianMetric J α hs ht)),
    ∃ hμ : IsProbabilityMeasure μ, letI := hμ
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
        ‖S.regularize (hermitianMetric J α hs ht) μ‖^2 ≤ C/r^2 ∧
        ∀ V : L2 A J α hs ht true,
          (∀ a : PreL2 A J α hs ht true,
            ⟪V,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
              (a-preAntiProjection A J α hs ht a))⟫ = 0) →
          |⟪S.regularize (hermitianMetric J α hs ht) μ,V⟫| ≤ K*‖V‖ := by
  obtain ⟨μ,hμ,-,-,hann,-⟩ := exists_geometric_separating_current J α hs ht hn
  let := hμ
  exact ⟨μ,hμ,separating_current_mass_and_cross A J α hs ht E hE D hD μ hann⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]

lemma finite_common_parametrix_partition
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J) :
    ∃ A : FiniteCharts X,
      (∀ p : A.centers, tsupport (A.partition p) ⊆ (parametrixData J α hs ht p.val).source) ∧
      (∀ p : A.centers, tsupport (A.partition p) ⊆ (HodgeChart.data J α hs ht p.val).source) := by
  classical
  let U : X → Set X := fun p => (parametrixData J α hs ht p).source ∩
    (HodgeChart.data J α hs ht p).source
  have hU (p : X) : IsOpen (U p) :=
    (parametrixData J α hs ht p).source_open.inter (HodgeChart.data J α hs ht p).source_open
  have hp (p : X) : p ∈ U p :=
    ⟨(parametrixData J α hs ht p).mem_source,(HodgeChart.data J α hs ht p).mem_source⟩
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun p _ => mem_iUnion_of_mem p (hp p))
  have hc : (univ : Set X) ⊆ ⋃ p : s, U p.val := by
    intro x hx
    obtain ⟨p,hp',hxp⟩ := mem_iUnion₂.mp (hscover hx)
    exact mem_iUnion_of_mem ⟨p,hp'⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => U p.val) (fun p => hU p.val) hc
  let A : FiniteCharts X := ⟨s,ρ,fun p => (hρ p).trans
    (inter_subset_left.trans (parametrixData J α hs ht p.val).source_subset)⟩
  exact ⟨A,fun p => (hρ p).trans inter_subset_left,
    fun p => (hρ p).trans inter_subset_right⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
