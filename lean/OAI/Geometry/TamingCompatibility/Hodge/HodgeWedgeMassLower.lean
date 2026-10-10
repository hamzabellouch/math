import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCorrectionLimit
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSeparatingMass
import OAI.Geometry.TamingCompatibility.Hodge.HodgeAngularPoint

namespace OAI

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

include hE in
lemma same_resolvent_wedge_mass_lower :
    let := geometricMetricSpace J α hs ht
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ],
      ∀ M : ℝ, 0 ≤ M →
      (∀ x : X, ∀ s : ℝ, 0 < s →
        μ.real {v | ENNReal.ofReal (dist x v.val.proj) < ENNReal.ofReal s} ≤ M*s^2) →
      ∀ (r : ℝ) (hr : 0 < r),
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
        -(C*M+B) ≤ ⟪S.regularize (hermitianMetric J α hs ht) μ,
          l2Star A J α hs ht (S.regularize (hermitianMetric J α hs ht) μ)⟫ := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨C,B,hC,hB,hbound⟩ := same_resolvent_wedge_point_lower A J α hs ht E hE D hD 6 0
  refine ⟨8*C,B,mul_nonneg (by norm_num) hC,hB,?_⟩
  intro μ _ M hM hgrowth r hr S
  let g := hermitianMetric J α hs ht
  have hb : Continuous (fun v : MetricUnit g => v.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  let P : X → MetricUnit g → ℝ := fun x v => ((1+dist x v.val.proj/r)⁻¹)^6
  have hm (x : X) : Measurable (fun v : MetricUnit g => ENNReal.ofReal (dist x v.val.proj)) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.dist hb)).measurable
  have hp (x : X) : Continuous (P x) := by
    apply Continuous.pow
    apply Continuous.inv₀
    · exact continuous_const.add ((continuous_const.dist hb).div_const r)
    · intro v
      have h : 0 < 1+dist x v.val.proj/r := by positivity
      exact h.ne'
  have hi (x : X) : Integrable (P x) μ :=
    (hp x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint (x : X) : (∫ v, P x v ∂μ) ≤ 8*M*r^2 := by
    have hh := QuadraticShell.integral_profile_normalized_bound μ
      (fun v : MetricUnit g => ENNReal.ofReal (dist x v.val.proj)) (hm x) M hM (hgrowth x) hr
    have he (v : MetricUnit g) :
        (QuadraticShell.profile r (ENNReal.ofReal (dist x v.val.proj))).toReal = P x v := by
      rw [QuadraticShell.profile_ofReal hr dist_nonneg,ENNReal.toReal_ofReal (by positivity)]
    simp_rw [he] at hh
    exact (div_le_iff₀ (sq_pos_of_pos hr)).mp hh
  have hinner (u : MetricUnit g) : -(8*C*M+B) ≤ ∫ v, S.wedgeKernel g u v ∂μ := by
    have hk : Integrable (fun v => S.wedgeKernel g u v) μ :=
      ((S.wedgeKernel_continuous g).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc
      _ ≤ -(C/r^2)*(∫ v, P u.val.proj v ∂μ)-B := by
        have hh := mul_le_mul_of_nonpos_left (hint u.val.proj) (neg_nonpos.mpr (div_nonneg hC (sq_nonneg r)))
        have he : -(C/r^2)*(8*M*r^2)-B = -(8*C*M+B) := by field_simp; ring
        linarith
      _ = ∫ v, -(C/r^2)*P u.val.proj v-B ∂μ := by
        rw [integral_sub ((hi u.val.proj).const_mul _) (integrable_const _),
          integral_const_mul,integral_const,probReal_univ,one_smul]
      _ ≤ _ := integral_mono (((hi u.val.proj).const_mul _).sub (integrable_const _)) hk
        (fun v => by simpa [P,g] using hbound r hr S u v)
  have he (u : MetricUnit g) : (∫ v, S.wedgeKernel g u v ∂μ) =
      ⟪S.evaluationVector g u, ∫ v, l2Star A J α hs ht (S.evaluationVector g v) ∂μ⟫ := by
    have h := (innerSL ℝ (S.evaluationVector g u)).integral_comp_comm
      ((l2Star A J α hs ht).integrable_comp (S.evaluationVector_integrable g μ))
    simpa only [innerSL_apply_apply,HodgeSmoothingCover.wedgeKernel] using h
  have hk : Integrable (fun u => ∫ v, S.wedgeKernel g u v ∂μ) μ := by
    simp_rw [he]
    exact (S.evaluationVector_integrable g μ).inner_const _
  have hh := integral_mono (integrable_const (μ := μ) (-(8*C*M+B))) hk hinner
  rw [integral_const,probReal_univ,one_smul,← S.regularize_wedge g μ μ] at hh
  exact hh

include hE in
lemma separating_current_wedge_lower
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (r : ℝ) (hr : 0 < r),
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
      -L ≤ ⟪S.regularize (hermitianMetric J α hs ht) μ,
          l2Star A J α hs ht (S.regularize (hermitianMetric J α hs ht) μ)⟫ := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨M,hM,hgrowth⟩ := separating_probability_quadratic_growth J α hs ht μ hann
  have hg : ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {v | ENNReal.ofReal (dist x v.val.proj) < ENNReal.ofReal s} ≤ M*s^2 := by
    intro x s hs'
    simpa only [← edist_dist,geometric_edist_eq J α hs ht] using hgrowth x s hs'
  obtain ⟨C,B,hC,hB,hbound⟩ := same_resolvent_wedge_mass_lower A J α hs ht E hE D hD
  exact ⟨C*M+B,by positivity,fun r hr S => hbound μ M hM hg r hr S⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
open Filter
open scoped Topology RealInnerProductSpace
namespace TamingCompatibility.GeometricHilbert
lemma weak_limit_functional_represented
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Φ : V →ₗ[ℝ] ℝ) (q : ℝ → UniformSpace.Completion V) (M : ℝ)
    (hbound : ∀ᶠ r in 𝓝[>] (0:ℝ), ‖q r‖ ≤ M)
    (hconv : ∀ v : V, Tendsto (fun r : ℝ => ⟪q r,(v : UniformSpace.Completion V)⟫)
      (𝓝[>] (0:ℝ)) (𝓝 (Φ v))) :
    ∃ Q : UniformSpace.Completion V, ∀ v : V, ⟪Q,(v : UniformSpace.Completion V)⟫ = Φ v := by
  have hΦ (v : V) : ‖Φ v‖ ≤ M*‖v‖ := by
    apply le_of_tendsto (hconv v).norm
    filter_upwards [hbound] with r hr
    calc
      ‖⟪q r,(v : UniformSpace.Completion V)⟫‖ ≤ ‖q r‖*‖(v : UniformSpace.Completion V)‖ := norm_inner_le_norm _ _
      _ ≤ M*‖v‖ := by rw [UniformSpace.Completion.norm_coe]; exact mul_le_mul_of_nonneg_right hr (norm_nonneg v)
  let F : V →L[ℝ] ℝ := Φ.mkContinuous M hΦ
  refine ⟨(InnerProductSpace.toDual ℝ (UniformSpace.Completion V)).symm F.fromCompletion,fun v => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply,ContinuousLinearMap.fromCompletion_apply_coe]
  rfl
end TamingCompatibility.GeometricHilbert

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.GeometricHilbert
lemma norm_bound_of_wedge_energy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (p q : V) (w L K : ℝ) (hL : 0 ≤ L)
    (hw : -L ≤ w) (hc : |⟪p,q⟫| ≤ K*‖q‖)
    (he : w+2*⟪p,q⟫+‖q‖^2 = 0) : ‖q‖ ≤ K+Real.sqrt (K^2+L) := by
  have hh := (neg_le_abs ⟪p,q⟫).trans hc
  have hr := Real.sq_sqrt (show 0 ≤ K^2+L by positivity)
  have hn := Real.sqrt_nonneg (K^2+L)
  by_contra h
  have h' : K+Real.sqrt (K^2+L) < ‖q‖ := lt_of_not_ge h
  nlinarith [sq_nonneg (‖q‖-K-Real.sqrt (K^2+L))]
end TamingCompatibility.GeometricHilbert

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricNormalCharts Filter
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ConnectedSpace X] [SecondCountableTopology X]
attribute [local instance] unitMeasurable unitBorel unitT2

theorem exists_counterexample_L2_data
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) (hc : IsClosed α)
    (hn : ¬ ∃ η : TwoForm X, IsSymplectic η ∧ Compatible η J) :
    ∃ A : FiniteCharts X,
    ∃ μ : Measure (MetricUnit (hermitianMetric J α hs ht)),
    ∃ hμ : IsProbabilityMeasure μ, letI := hμ
    ∃ Q : L2 A J α hs ht true,
      l2AntiProjection A J α hs ht Q = Q ∧
      l2Star A J α hs ht Q = Q ∧
      (∀ a : smoothForms X 2, IsClosed a.val →
        unitMeasureCurrent J (hermitianMetric J α hs ht) μ a+
          ⟪Q,smoothL2 A J α hs ht true a⟫ = 0) ∧
      ⟪Q,smoothL2 A J α hs ht true ⟨α,hs⟩⟫ = -1 ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ x : X, ∀ s : ℝ, 0 < s →
        μ.real {u | hermitianEDist J α hs ht x u.val.proj < ENNReal.ofReal s} ≤ M*s^2) := by
  obtain ⟨A,hE,hD⟩ := finite_common_parametrix_partition J α hs ht
  let E := fun p : A.centers => parametrixData J α hs ht p.val
  let D := fun p : A.centers => HodgeChart.data J α hs ht p.val
  obtain ⟨μ,hμ,-,-,hann,-⟩ := exists_geometric_separating_current J α hs ht hn
  let := hμ
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
  refine ⟨A,μ,hμ,Q,hQa,?_,?_,?_,separating_probability_quadratic_growth J α hs ht μ hann⟩
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
end
end

end OAI
