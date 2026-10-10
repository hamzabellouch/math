import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCorrectionLimit
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSeparatingMass
import OAI.Geometry.TamingCompatibility.Hodge.HodgeAngularPoint

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricNormalCharts
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ConnectedSpace X] [SecondCountableTopology X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

include hE in
lemma separating_current_wedge_upper
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
      ⟪S.regularize (hermitianMetric J α hs ht) μ,
          l2Star A J α hs ht (S.regularize (hermitianMetric J α hs ht) μ)⟫ ≤ K := by
  obtain ⟨B,hBc,hBR,L,hL,hB⟩ := exists_convergent_closed_lift A J α hs ht D hD (hermitianMetric J α hs ht)
  obtain ⟨C,K,hC,hK,hcross⟩ := separating_current_mass_and_cross A J α hs ht E hE D hD μ hann
  refine ⟨K^2,sq_nonneg _,fun r hr hr1 S => ?_⟩
  have hrep := ((hB μ).1 r hr hr1).1
  have hcr := (hcross r hr hr1 S).2
    (hodgeCorrectionRegularize A J α hs ht D hD B (hermitianMetric J α hs ht) μ r hr) (by
      intro a
      rw [hrep,map_sub,hodgeCorrectionSource_anti,sub_self])
  have he := hodgeCorrected_energy_identity A J α hs ht D hD B hBc hBR
    (hermitianMetric J α hs ht) μ hann r hr S hrep
  have hh := (neg_le_abs ⟪S.regularize (hermitianMetric J α hs ht) μ,
    hodgeCorrectionRegularize A J α hs ht D hD B (hermitianMetric J α hs ht) μ r hr⟫).trans hcr
  nlinarith [sq_nonneg (‖hodgeCorrectionRegularize A J α hs ht D hD B (hermitianMetric J α hs ht) μ r hr‖-K)]

end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set MeasureTheory
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
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE in
lemma same_resolvent_angularNear_point :
    let := geometricMetricSpace J α hs ht
    ∃ T c C B : ℝ, 0 < T ∧ 0 < c ∧ 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (r : ℝ) (hr : 0 < r), 2*r^2 ≤ T →
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
      ∀ p : A.centers, ∀ uv : UnitPair J α hs ht,
        c*(r⁻¹)^4*angularNear A J α hs ht E r p uv ≤
          S.wedgeKernel (hermitianMetric J α hs ht) uv.1 uv.2 +
            (C/r^2)*((1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹)^6+B := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,C,B,hT,hC,hB,hpoint⟩ := same_resolvent_wedge_point_angular A J α hs ht E hE D hD 6 0
  obtain ⟨C₀,B₀,hC₀,hB₀,hlower⟩ := same_resolvent_wedge_point_lower A J α hs ht E hE D hD 6 0
  let c := (1/2 : ℝ)*((1/(120*(4*Real.pi)^2))*Real.exp (-(9/4 : ℝ)))
  refine ⟨T,c,C+C₀,B+B₀,hT,by dsimp [c]; positivity,by positivity,by positivity,?_⟩
  intro r hr hrT S p uv
  have hp : 0 ≤ ((1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹)^6 := by positivity
  have hcdiv : 0 ≤ C₀/r^2 := div_nonneg hC₀ (sq_nonneg r)
  have hdiv : (C+C₀)/r^2 = C/r^2+C₀/r^2 := add_div _ _ _
  by_cases huv : uv ∈ angularNearSet A J α hs ht E r p
  · have hb := angularCoordinates_bases A J α hs ht E p huv.1
    have hh := hpoint r hr S p (angularCoordinates A J α hs ht E p uv)
      (angularCoordinates_mem A J α hs ht E p huv.1) uv.1 uv.2 hb.1 hb.2
    have hl := HodgeKernelBounds.leading_lower hr (norm_nonneg _) huv.2 hrT
    have hmul := mul_le_mul_of_nonneg_right hl (angularWeight_nonneg A J α hs ht E p uv)
    have he : (1/2 : ℝ)*(coordinatePartition A p (angularCoordinates A J α hs ht E p uv).1 *
        (E p).normalCutoff (angularCoordinates A J α hs ht E p uv).2 *
        HodgeKernelBounds.leading r T ‖(angularCoordinates A J α hs ht E p uv).2‖) *
        (normalAngular A J α hs ht E p (angularCoordinates A J α hs ht E p uv) uv.1 uv.2)^2 =
      (1/2 : ℝ)*HodgeKernelBounds.leading r T ‖(angularCoordinates A J α hs ht E p uv).2‖ *
        angularWeight A J α hs ht E p uv := by dsimp [angularWeight]; ring
    rw [he] at hh
    simp only [Nat.mul_zero,pow_zero,mul_one] at hh
    rw [angularNear,indicator_of_mem huv,hdiv]
    dsimp [c]
    nlinarith [mul_nonneg hcdiv hp]
  · rw [angularNear,indicator_of_notMem huv,mul_zero,hdiv]
    have hh := hlower r hr S uv.1 uv.2
    simp only [Nat.mul_zero,pow_zero,mul_one] at hh
    have hn : 0 ≤ (C/r^2)*((1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹)^6 :=
      mul_nonneg (div_nonneg hC (sq_nonneg r)) hp
    nlinarith

omit [MeasurableSpace X] [BorelSpace X] in
lemma physicalProfile_integrable {r : ℝ} (hr : 0 < r)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    let := geometricMetricSpace J α hs ht
    Integrable (fun uv : UnitPair J α hs ht => ((1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹)^6) (μ.prod μ) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  have hb := angularBase_continuous J α hs ht
  have h : Continuous (fun uv : UnitPair J α hs ht => ((1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹)^6) :=
    (continuous_const.add ((hb.snd.dist hb.fst).div_const r)).inv₀ (fun uv => by
      have : 0 < 1+dist uv.1.val.proj uv.2.val.proj/r := by positivity
      exact this.ne') |>.pow 6
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [MeasurableSpace X] [BorelSpace X] in
lemma physicalProfile_integral_bound
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (M : ℝ) (hM : 0 ≤ M)
    (hgrowth : ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {u | hermitianEDist J α hs ht x u.val.proj < ENNReal.ofReal s} ≤ M*s^2)
    {r : ℝ} (hr : 0 < r) :
    let := geometricMetricSpace J α hs ht
    (∫ uv : UnitPair J α hs ht, ((1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹)^6 ∂μ.prod μ) ≤ 8*M*r^2 := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  have hb : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hi := physicalProfile_integrable J α hs ht hr μ
  rw [integral_prod _ hi]
  have hbnd (u : MetricUnit (hermitianMetric J α hs ht)) :
      (∫ v, ((1+dist u.val.proj v.val.proj/r)⁻¹)^6 ∂μ) ≤ 8*M*r^2 := by
    have hg : ∀ s : ℝ, 0 < s →
        μ.real {v | ENNReal.ofReal (dist u.val.proj v.val.proj) < ENNReal.ofReal s} ≤ M*s^2 := by
      intro s hsp
      simpa only [← edist_dist,geometric_edist_eq J α hs ht] using hgrowth u.val.proj s hsp
    have hm : Measurable (fun v : MetricUnit (hermitianMetric J α hs ht) => ENNReal.ofReal (dist u.val.proj v.val.proj)) :=
      (ENNReal.continuous_ofReal.comp (continuous_const.dist hb)).measurable
    have hh := QuadraticShell.integral_profile_normalized_bound μ
      (fun v : MetricUnit (hermitianMetric J α hs ht) => ENNReal.ofReal (dist u.val.proj v.val.proj)) hm M hM hg hr
    have he (v : MetricUnit (hermitianMetric J α hs ht)) :
        (QuadraticShell.profile r (ENNReal.ofReal (dist u.val.proj v.val.proj))).toReal =
          ((1+dist u.val.proj v.val.proj/r)⁻¹)^6 := by
      rw [QuadraticShell.profile_ofReal hr dist_nonneg,ENNReal.toReal_ofReal (by positivity)]
    simp_rw [he] at hh
    exact (div_le_iff₀ (sq_pos_of_pos hr)).mp hh
  calc
    _ ≤ ∫ _ : MetricUnit (hermitianMetric J α hs ht), 8*M*r^2 ∂μ :=
      integral_mono hi.integral_prod_left (integrable_const _) hbnd
    _ = _ := by rw [integral_const,probReal_univ,one_smul]

include hE hD in
lemma separating_current_angular_moment
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ p : A.centers,
      (∫ uv, angularNear A J α hs ht E r p uv ∂μ.prod μ) ≤ K*r^4 := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,c,C,B,hT,hc,hC,hB,hpoint⟩ := same_resolvent_angularNear_point A J α hs ht E hE D hD
  obtain ⟨M,hM,hgrowth⟩ := separating_probability_quadratic_growth J α hs ht μ hann
  obtain ⟨K,hK,hupper⟩ := separating_current_wedge_upper A J α hs ht E hE D hD μ hann
  let ρ := min 1 (Real.sqrt T/2)
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos (Real.sqrt_pos.mpr hT) (by norm_num))
  refine ⟨ρ,(K+8*C*M+B)/c,hρ,by positivity,?_⟩
  intro r hr hrρ p
  have hr1 : r ≤ 1 := hrρ.trans (min_le_left _ _)
  have hrt : r ≤ Real.sqrt T/2 := hrρ.trans (min_le_right _ _)
  have hrT : 2*r^2 ≤ T := by
    have hh := Real.sq_sqrt hT.le
    have hsqrt := Real.sqrt_nonneg T
    nlinarith
  let S := hodgeSmoothingCover A J α hs ht D hD r hr
  let g := hermitianMetric J α hs ht
  let W := fun uv : UnitPair J α hs ht => S.wedgeKernel g uv.1 uv.2
  let P := fun uv : UnitPair J α hs ht => ((1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹)^6
  have hW : Integrable W (μ.prod μ) :=
    (S.wedgeKernel_continuous g).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP : Integrable P (μ.prod μ) := physicalProfile_integrable J α hs ht hr μ
  have hA := angularNear_integrable A J α hs ht E hE r p μ
  have hh := integral_mono (hA.const_mul (c*(r⁻¹)^4))
    ((hW.add (hP.const_mul (C/r^2))).add (integrable_const B)) (hpoint r hr hrT S p)
  change (∫ uv, c*(r⁻¹)^4*angularNear A J α hs ht E r p uv ∂μ.prod μ) ≤
    ∫ uv, W uv+(C/r^2)*P uv+B ∂μ.prod μ at hh
  have hWP : Integrable (fun uv => W uv+(C/r^2)*P uv) (μ.prod μ) := hW.add (hP.const_mul _)
  rw [integral_const_mul,integral_add hWP (integrable_const B),
    integral_add hW (hP.const_mul (C/r^2)),integral_const_mul,integral_const,probReal_univ,one_smul] at hh
  have he : (∫ uv, W uv ∂μ.prod μ) =
      ⟪S.regularize g μ,l2Star A J α hs ht (S.regularize g μ)⟫ := by
    rw [integral_prod _ hW]
    exact (S.regularize_wedge g μ μ).symm
  have hp := mul_le_mul_of_nonneg_left (physicalProfile_integral_bound J α hs ht μ M hM hgrowth hr)
    (div_nonneg hC (sq_nonneg r))
  have hps : (C/r^2)*(8*M*r^2) = 8*C*M := by field_simp
  rw [hps] at hp
  rw [he] at hh
  have hw := hupper r hr hr1 S
  have hbnd : c*(r⁻¹)^4*(∫ uv, angularNear A J α hs ht E r p uv ∂μ.prod μ) ≤ K+8*C*M+B := by
    linarith
  have hpos : 0 < c*(r⁻¹)^4 := by positivity
  have hb : (∫ uv, angularNear A J α hs ht E r p uv ∂μ.prod μ) ≤ (K+8*C*M+B)/(c*(r⁻¹)^4) :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hbnd)
  have hid : (K+8*C*M+B)/(c*(r⁻¹)^4) = (K+8*C*M+B)/c*r^4 := by field_simp
  exact hb.trans_eq hid

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
