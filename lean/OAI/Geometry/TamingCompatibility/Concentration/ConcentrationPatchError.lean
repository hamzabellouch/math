import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationDifferential
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationPhysicalBound
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationFirstEstimate
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationCompare
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationVariationLimit
import OAI.Geometry.TamingCompatibility.DifferentialForms.SecondVariationLimit

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Hermitian Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (G : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hG : ∀ p, tsupport (A.partition p) ⊆ (G p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE hD hG in
lemma concentrationPatch_error_control
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (p : A.centers) :
    ∃ e : ℝ → MetricUnit (hermitianMetric J α hs ht) → ℝ,
      (∀ r, 0 < r → ∀ u, 0 ≤ e r u) ∧
      (∀ r, 0 < r → Integrable (e r) μ) ∧
      Tendsto (fun r => ∫ u, e r u ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ u,
        |eval (ManifoldForms.wedgeOne (scalarDifferential (concentrationPatch A J α hs ht E μ p r)) θ.val)
          u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ≤
        C*(globalConcentration A J α hs ht E μ r u.val.proj+e r u) := by
  let := geometricVolume_finite A J α hs ht
  let q := l2Coefficients A J α hs ht E hE Q
  have hq : Integrable q (geometricVolume A J α) := (Lp.memLp q).integrable (by norm_num)
  obtain ⟨a,b,ha,hb,hcomp⟩ := localConcentration_global_compare A J α hs ht E hE μ p
  obtain ⟨B,C,L,hB,hC,hL,hplane⟩ := concentration_plane_estimate A J α hs ht E hE μ Q hT p
  let v₁ := fun r u => ∫ v, variationDensity A J α hs ht E p r (v,u) ∂μ
  let v₂ := fun r u => ∫ v, secondVariationDensity A J α hs ht E p r (v,u) ∂μ
  let e := fun r u => B*physicalQError A J α hs ht q L r u.val.proj+(b+C)*r^4+v₁ r u+v₂ r u
  have hv₁ (r) (u) : 0 ≤ v₁ r u := integral_nonneg (fun v => variationDensity_nonneg A J α hs ht E p r (v,u))
  have hv₂ (r) (u) : 0 ≤ v₂ r u := integral_nonneg (fun v => secondVariationDensity_nonneg A J α hs ht E p r (v,u))
  have he (r) (hr : 0 < r) (u) : 0 ≤ e r u := by
    exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg hB (physicalQError_nonneg A J α hs ht q hr _))
      (mul_nonneg (add_nonneg hb hC) (by positivity))) (hv₁ r u)) (hv₂ r u)
  have hi₁ (r) (hr : 0 < r) : Integrable (v₁ r) μ :=
    (variationDensity_integrable A J α hs ht E hE μ p hr).integral_prod_right
  have hi₂ (r) (hr : 0 < r) : Integrable (v₂ r) μ :=
    (secondVariationDensity_integrable A J α hs ht E hE μ p hr).integral_prod_right
  have hqi (r) (hr : 0 < r) := physicalQError_integrable A J α hs ht μ q hq hL hr
  have hei (r) (hr : 0 < r) : Integrable (e r) μ :=
    (((hqi r hr).const_mul B).add (integrable_const ((b+C)*r^4))).add (hi₁ r hr) |>.add (hi₂ r hr)
  have hiEq (r) (hr : 0 < r) : (∫ u, e r u ∂μ) =
      B*(∫ u, physicalQError A J α hs ht q L r u.val.proj ∂μ)+(b+C)*r^4+
      (∫ uv, variationDensity A J α hs ht E p r uv ∂μ.prod μ)+
      (∫ uv, secondVariationDensity A J α hs ht E p r uv ∂μ.prod μ) := by
    erw [show e r = (fun u => B*physicalQError A J α hs ht q L r u.val.proj+(b+C)*r^4+v₁ r u+v₂ r u) from rfl,
      integral_add ((((hqi r hr).const_mul B).add (integrable_const ((b+C)*r^4))).add (hi₁ r hr)) (hi₂ r hr),
      integral_add (((hqi r hr).const_mul B).add (integrable_const ((b+C)*r^4))) (hi₁ r hr),
      integral_add ((hqi r hr).const_mul B) (integrable_const ((b+C)*r^4)),integral_const_mul,
      integral_const,probReal_univ,one_smul]
    have h1 : (∫ u, v₁ r u ∂μ) = ∫ uv, variationDensity A J α hs ht E p r uv ∂μ.prod μ :=
      (integral_prod_symm _ (variationDensity_integrable A J α hs ht E hE μ p hr)).symm
    have h2 : (∫ u, v₂ r u ∂μ) = ∫ uv, secondVariationDensity A J α hs ht E p r uv ∂μ.prod μ :=
      (integral_prod_symm _ (secondVariationDensity_integrable A J α hs ht E hE μ p hr)).symm
    rw [h1,h2]
  have he0 : Tendsto (fun r => ∫ u, e r u ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h0 := physicalQError_limit A J α hs ht μ hann q (Lp.memLp q) hL
    have h1 := separating_current_variation_limit A J α hs ht E hE D hD G hG μ hann p
    have h2 := separating_current_second_variation_limit A J α hs ht E hE D hD G hG μ hann p
    have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    have htend := (((h0.const_mul B).add ((hr.pow 4).const_mul (b+C))).add h1).add h2
    simp only [zero_pow (by decide : (4:ℕ) ≠ 0),mul_zero,add_zero] at htend
    apply htend.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hiEq r hr).symm
  refine ⟨e,he,hei,he0,fun θ => ?_⟩
  obtain ⟨K,hK,hbound⟩ := concentrationPatch_tangential_bound A J α hs ht E hE p θ
  refine ⟨K*(a+1),by positivity,fun r hr u => ?_⟩
  by_cases hx : u.val.proj ∈ tsupport (A.partition p)
  · have hh := hbound μ r hr u hx
    change |eval _ u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ≤ _ at hh
    have hp := hplane r hr u
    have hb' := hcomp u.val.proj hx r hr
    have hF := globalConcentration_nonneg A J α hs ht E μ r u.val.proj
    have hsum : localConcentration A J α hs ht E μ p r (unitChartBase J α hs ht p.val u)+
        A.partition p u.val.proj *
          (|fderiv ℝ (localConcentration A J α hs ht E μ p r) (unitChartBase J α hs ht p.val u) (unitChartFirst J α hs ht p.val u)|+
           |fderiv ℝ (localConcentration A J α hs ht E μ p r) (unitChartBase J α hs ht p.val u) (unitChartSecond J α hs ht p.val u)|) ≤
        (a+1)*(globalConcentration A J α hs ht E μ r u.val.proj+e r u) := by
      have hen := he r hr u
      dsimp only [e,v₁,v₂,unitChartBase,q] at hp hb' hen ⊢
      nlinarith
    exact hh.trans ((mul_le_mul_of_nonneg_left hsum hK).trans_eq (by ring))
  · unfold eval
    rw [concentrationPatch_wedge_zero_off A J α hs ht E μ p r θ.val hx]
    change |(0 : ℝ)| ≤ _
    rw [abs_zero]
    exact mul_nonneg (by positivity) (add_nonneg (globalConcentration_nonneg A J α hs ht E μ r _) (he r hr u))
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Hermitian Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE in
omit [MeasurableSpace X] [BorelSpace X] in
lemma localConcentration_gradient_bound
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ] (p : A.centers) :
    ∃ B C L : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ 0 < L ∧ ∀ x : X, x ∈ tsupport (A.partition p) →
      ∀ r : ℝ, 0 < r →
      ‖fderiv ℝ (localConcentration A J α hs ht E μ p r) (extChartAt Model p.val x)‖ ≤
        B*physicalGradientMass J α hs ht μ L r x+C*r^4 := by
  obtain ⟨L,hL,hprofile⟩ := compact_chart_profile_bound J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  obtain ⟨_,P,_,hP,harea⟩ := unitChartArea_bounds J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  have hone : ∀ z : Space, ‖z‖ < (E p).concentrationCutoff.radius/2 → (E p).concentrationCutoff.bump z = 1 := by
    intro z hz
    apply ContDiffBump.one_of_mem_closedBall
    change dist z 0 ≤ (E p).concentrationCutoff.radius/2
    simpa only [dist_zero_right] using hz.le
  obtain ⟨C,hC,hder⟩ := cutKernel_gradient_bound
    (E p).concentrationCutoff.bump (E p).concentrationCutoff.bump.contDiff
    (E p).concentrationCutoff.bump.hasCompactSupport
    (fun z => (E p).concentrationCutoff.bump.nonneg (x := z))
    (fun z => (E p).concentrationCutoff.bump.le_one (x := z))
    (by linarith [(E p).concentrationCutoff.positive] : 0 < (E p).concentrationCutoff.radius/2) hone
  refine ⟨48*P,P*C,L,by positivity,by positivity,hL,fun x hx r hr => ?_⟩
  let f := fun u : MetricUnit (hermitianMetric J α hs ht) =>
    (48*P/r^3)*physicalProfile J α hs ht (L*r) x u.val.proj+P*C*r^4
  have hp : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hf : Integrable f μ := by
    exact (((physicalProfile_continuous J α hs ht (mul_pos hL hr)).comp
      (continuous_const.prodMk hp)).const_mul _ |>.add continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hn (u) : 0 ≤ f u := add_nonneg
    (mul_nonneg (by positivity) (physicalProfile_nonneg J α hs ht _ _ _)) (by positivity)
  have he : ∫ u, f u ∂μ = 48*P*physicalGradientMass J α hs ht μ L r x+P*C*r^4 := by
    have hi : Integrable (fun u : MetricUnit (hermitianMetric J α hs ht) => (48*P/r^3)*physicalProfile J α hs ht (L*r) x u.val.proj) μ := (((physicalProfile_continuous J α hs ht (mul_pos hL hr)).comp
      (continuous_const.prodMk hp)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul (48*P/r^3)
    rw [show f = (fun u => (48*P/r^3)*physicalProfile J α hs ht (L*r) x u.val.proj+P*C*r^4) from rfl,
      integral_add hi (integrable_const _),integral_const_mul,integral_const,probReal_univ,one_smul]
    dsimp only [physicalGradientMass,physicalProfileMass]
    ring
  apply ContinuousLinearMap.opNorm_le_bound _ (by rw [←he]; exact integral_nonneg hn)
  intro w
  change ‖fderiv ℝ (planeConvolution J α hs ht p.val (E p).concentrationCompact μ
    (cutKernel (E p).concentrationCutoff.bump r)) (extChartAt Model p.val x) w‖ ≤ _
  rw [planeConvolution_deriv J α hs ht p.val (E p).concentrationCompact_compact
    (E p).concentrationCompact_target μ _ (cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff)
    (cutKernel_compact _ (E p).concentrationCutoff.bump.hasCompactSupport r),←he,←integral_mul_const]
  apply norm_integral_le_of_norm_le (hf.mul_const ‖w‖)
  apply ae_of_all
  intro u
  by_cases hu : u ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
  · rw [indicator_of_mem hu,norm_mul,Real.norm_eq_abs,abs_of_nonneg
      (show 0 ≤ unitChartArea J α hs ht p.val u from mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    have hprof := hprofile x (A.subordinate p hx)
      ((E p).concentrationCompact_center (partition_center_ball A J α ht E hE p hx)) u hu r hr
    have hd := (hder r hr (extChartAt Model p.val x-unitChartBase J α hs ht p.val u)).trans
      (add_le_add (mul_le_mul_of_nonneg_left hprof (by positivity : 0 ≤ 48/r^3)) le_rfl)
    have hw := (fderiv ℝ (cutKernel (E p).concentrationCutoff.bump r)
      (extChartAt Model p.val x-unitChartBase J α hs ht p.val u)).le_opNorm w
    have hww := hw.trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
    exact (mul_le_mul (harea u hu).2 hww (norm_nonneg _) hP.le).trans_eq (by dsimp only [f]; ring)
  · rw [indicator_of_notMem hu,norm_zero]
    exact mul_nonneg (hn u) (norm_nonneg _)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
