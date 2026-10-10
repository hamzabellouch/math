import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothLimit
import OAI.Geometry.TamingCompatibility.Hodge.HodgeL2
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSubprobMass

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set MeasureTheory Filter
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

include hE hD in
lemma subprob_anti_cross_bound
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (hμ : μ.real univ ≤ 1) (M : ℝ) (hM : 0 ≤ M)
    (hgrowth : ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {v | hermitianEDist J α hs ht x v.val.proj < ENNReal.ofReal s} ≤ M*s^2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ V : L2 A J α hs ht true, l2AntiProjection A J α hs ht V = V →
      |⟪hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) μ r,
        hodgeRegularization A J α hs ht r V⟫| ≤ K*‖V‖ := by
  let := geometricMetricSpace J α hs ht
  have hg : ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {v | ENNReal.ofReal (dist x v.val.proj) < ENNReal.ofReal s} ≤ M*s^2 := by
    intro x s hs'
    simpa only [← edist_dist,geometric_edist_eq J α hs ht] using hgrowth x s hs'
  obtain ⟨K,hK,hbound⟩ := same_resolvent_subprob_current_mass_cross A J α hs ht E hE D hD
    (hermitianMetric J α hs ht) μ hμ M hM hg
  refine ⟨K,hK,fun r hr hr1 V hV => ?_⟩
  simp only [hodgePositiveCurrentFamily,dite_eq_left hr]
  exact (hbound r hr hr1 _ _ (hodgeRegularization_anti_source A J α hs ht V hV hr)).trans
    (mul_le_mul_of_nonneg_left (hodgeRegularization_norm_le A J α hs ht r V) hK)

include hE hD in
lemma subprob_anti_cross_tendsto
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (hμ : μ.real univ ≤ 1) (M : ℝ) (hM : 0 ≤ M)
    (hgrowth : ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {v | hermitianEDist J α hs ht x v.val.proj < ENNReal.ofReal s} ≤ M*s^2)
    (Q : L2 A J α hs ht true) (hQ : l2AntiProjection A J α hs ht Q = Q) :
    Tendsto (fun r : ℝ => ⟪hodgePositiveCurrentFamily A J α hs ht D hD
      (hermitianMetric J α hs ht) μ r,hodgeRegularization A J α hs ht r Q⟫)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K,hK,hbound⟩ := subprob_anti_cross_bound A J α hs ht E hE D hD μ hμ M hM hgrowth
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨a,ha⟩ := smoothAntiProjection_dense A J α hs ht Q hQ (ε/(2*(K+1))) (by positivity)
  let b := smoothL2 A J α hs ht true (preAntiProjection A J α hs ht a)
  have hb : l2AntiProjection A J α hs ht b = b := by
    dsimp only [b]
    rw [preAntiProjection_smooth,l2AntiProjection_idempotent]
  have hdiff : l2AntiProjection A J α hs ht (Q-b) = Q-b := by rw [map_sub,hQ,hb]
  have hsmall : K*‖Q-b‖ < ε/2 := by
    have hh : ‖Q-b‖ < ε/(2*(K+1)) := by simpa only [b,norm_sub_rev] using ha
    have ht' := (lt_div_iff₀ (show 0 < 2*(K+1) by positivity)).mp hh
    nlinarith [norm_nonneg (Q-b)]
  have hl := hodgePositiveCurrentFamily_anti_cross_tendsto A J α hs ht D hD
    (hermitianMetric J α hs ht) μ a
  have he := (Metric.tendsto_nhds.mp hl) (ε/2) (by positivity)
  have hl1 : ∀ᶠ r in 𝓝[>] (0:ℝ), r < 1 :=
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0) (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin,hl1,he] with r hr hr1 he
  change 0 < r at hr
  let P := hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) μ r
  have hd : |⟪P,hodgeRegularization A J α hs ht r (Q-b)⟫| < ε/2 :=
    (hbound r hr hr1.le (Q-b) hdiff).trans_lt hsmall
  have he' : |⟪P,hodgeRegularization A J α hs ht r b⟫| < ε/2 := by
    simpa only [Real.dist_eq,sub_zero] using he
  have heq : ⟪P,hodgeRegularization A J α hs ht r Q⟫ =
      ⟪P,hodgeRegularization A J α hs ht r (Q-b)⟫+⟪P,hodgeRegularization A J α hs ht r b⟫ := by
    rw [map_sub,inner_sub_right]; ring
  rw [Real.dist_eq,sub_zero]
  change |⟪P,hodgeRegularization A J α hs ht r Q⟫| < ε
  rw [heq]
  exact (abs_add_le _ _).trans_lt (by linarith)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
