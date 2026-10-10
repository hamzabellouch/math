import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RawInterior
import OAI.Geometry.TamingCompatibility.Charts.LocalSmooth
import OAI.Geometry.TamingCompatibility.Functional.CompactCutoff

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma raw_smooth_near (p : A.centers) (q : Space) (hq : q ∈ (D p).domain)
    (hwq : coordinateWeight A p q ≠ 0)
    (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
    (heq : ∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) :
    ∃ τ : 𝓢(Space,ℝ), ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ (D p).domain ∧
      (∀ z ∈ V, τ z * coordinateWeight A p z = 1) ∧
      ∃ g : Space →ᵇ ScalarPair.F, ContDiff ℝ ∞ (g : Space → ScalarPair.F) ∧
      ∀ χ : 𝓢(Space,ℂ), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
        rawDistribution A J α hs ht D hD p τ u χ = EuclideanSobolev.boundedDistribution g χ := by
  obtain ⟨τ,-,-,U,hU,hqU,hUD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hq hwq
  obtain ⟨W,hW,hqW,hWU,hall⟩ := raw_interior_regular A J α hs ht D hD p τ hU hUD hτ q hqU f u heq
  obtain ⟨V,hV,hqV,hVW,g,hg,hgdist⟩ := exists_local_smooth_representative hW hqW hall
  refine ⟨τ,V,hV,hqV,hVW.trans (hWU.trans hUD),fun z hz => hτ z (hWU (hVW hz)),g,hg,?_⟩
  exact fun χ hc hχV => tests_eq_of_localize hV hgdist χ hc hχV

include hD in
omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma exists_nonzero_weight_chart (x : X) :
    ∃ p : A.centers, A.partition p x ≠ 0 ∧ (extChartAt Model p.val) x ∈ (D p).domain := by
  classical
  have hp : ∃ p : A.centers, A.partition p x ≠ 0 := by
    by_contra hn
    push Not at hn
    have hsum := partition_sum A x
    simp only [hn,Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  obtain ⟨p,hp⟩ := hp
  have hx := hD p (subset_closure hp)
  refine ⟨p,hp,(D p).small_ball_subset ?_⟩
  exact Metric.ball_subset_closedBall hx.2

end TamingCompatibility.GeometricHilbert

end

end OAI
