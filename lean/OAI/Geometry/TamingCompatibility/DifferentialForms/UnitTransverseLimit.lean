import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.CompactProfilePoint
import OAI.Geometry.TamingCompatibility.Charts.RadialAtlasProducer

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory RadialPotential PlaneVariation Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma unitTransverse_rational_limit (p : X) (b : Space) {R : ℝ} (hR : 0 < R)
    (hBT : Metric.closedBall b R ⊆ (extChartAt Model p).target)
    {K : Set Space} (hK : IsCompact K) (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (hdef : Integrable (smoothUnitDefect J α hs ht p b R 0) μ) :
    Tendsto (fun r : ℝ => ∫ u, radialCoefficient r (unitDistanceCut J α hs ht p b K u)*
      ‖unitTransverseCut J α hs ht p b K u‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply rational_defect_tendsto_zero _ _
    ((unitTransverseCut_measurable J α hs ht p b hK hKT).norm.pow_const 2)
    (unitDistanceCut_measurable J α hs ht p b hK hKT) (fun _ => by positivity)
    (fun u hu => by rw [unitTransverseCut_zero J α hs ht p b K u hu,norm_zero]; norm_num)
  exact unitTransverse_quotient_integrable J α hs ht p b hR hBT hK hKT μ hdef

lemma separating_probability_atlas_transverse_limit
    (A : FiniteCharts X) (D : ∀ p : A.centers, Data J α ht p.val)
    (hA : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (p : A.centers) (x : X) (hp : A.partition p x ≠ 0)
    {K : Set Space} (hK : IsCompact K) (hKT : K ⊆ (extChartAt Model p.val).target) :
    Tendsto (fun r : ℝ => ∫ u,
      radialCoefficient r (unitDistanceCut J α hs ht p.val (extChartAt Model p.val x) K u)*
        ‖unitTransverseCut J α hs ht p.val (extChartAt Model p.val x) K u‖^2 ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨R,hR,hBT,hdef⟩ := separating_probability_atlas_defect J α hs ht A D hA μ hann p x hp
  exact unitTransverse_rational_limit J α hs ht p.val _ hR hBT hK hKT μ hdef
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory RadialPotential PlaneVariation Concentration GeometricNormalCharts
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma unitTransverse_rational_measurable (p : X) (b : Space)
    {K : Set Space} (hK : IsCompact K) (hKT : K ⊆ (extChartAt Model p).target) (r : ℝ) :
    Measurable (fun u => radialCoefficient r (unitDistanceCut J α hs ht p b K u)*
      ‖unitTransverseCut J α hs ht p b K u‖^2) := by
  have hd := unitDistanceCut_measurable J α hs ht p b hK hKT
  have hv := unitTransverseCut_measurable J α hs ht p b hK hKT
  exact (measurable_const.div ((measurable_const.add (hd.pow_const 2)).pow_const 4)).mul (hv.norm.pow_const 2)

lemma separating_probability_transverse_uniform
    (p : X) {K : Set Space} (hK : IsCompact K) (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, x ∈ (extChartAt Model p).source →
      extChartAt Model p x ∈ K → ∀ r : ℝ, 0 < r →
      Integrable (fun u => radialCoefficient r (unitDistanceCut J α hs ht p (extChartAt Model p x) K u)*
        ‖unitTransverseCut J α hs ht p (extChartAt Model p x) K u‖^2) μ ∧
      (∫ u, radialCoefficient r (unitDistanceCut J α hs ht p (extChartAt Model p x) K u)*
        ‖unitTransverseCut J α hs ht p (extChartAt Model p x) K u‖^2 ∂μ) ≤ C := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨M,hM,hgrowth⟩ := separating_probability_quadratic_growth J α hs ht μ hann
  obtain ⟨L₀,hL₀⟩ := chartInverse_compact_lipschitz J α hs ht p K hK hKT
  let L : ℝ := (L₀:ℝ)+1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨64*M*L^2,by positivity,fun x hx hxK r hr => ?_⟩
  let P : MetricUnit (hermitianMetric J α hs ht) → ℝ :=
    fun u => ((1+dist x u.val.proj/(L*r))⁻¹)^6
  have hLr : 0 < L*r := mul_pos hL hr
  have hb : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hp : Continuous P := ((continuous_const.add ((continuous_const.dist hb).div_const (L*r))).inv₀
    (fun u => (show 0 < 1+dist x u.val.proj/(L*r) by positivity).ne')).pow 6
  have hpi : Integrable P μ := hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound (u : MetricUnit (hermitianMetric J α hs ht)) :
      radialCoefficient r (unitDistanceCut J α hs ht p (extChartAt Model p x) K u)*
        ‖unitTransverseCut J α hs ht p (extChartAt Model p x) K u‖^2 ≤ (8/r^2)*P u := by
    by_cases hu : u ∈ unitChartDomain J α hs ht p K
    · rw [unitDistanceCut,unitTransverseCut,indicator_of_mem hu,indicator_of_mem hu]
      have humem := unitChart_mem J α hs ht p hKT hu
      obtain ⟨h₁,h₂,h₃,_⟩ := unitChartPlane J α hs ht p u humem.1
      have hv := norm_transverse_le (unitChartFirst J α hs ht p u) (unitChartSecond J α hs ht p u)
        (unitChartBase J α hs ht p u-extChartAt Model p x) h₁ h₂ h₃
      have hphys := hL₀.dist_le_mul _ hxK _ humem.2
      change dist ((extChartAt Model p).symm (extChartAt Model p x))
        ((extChartAt Model p).symm (unitChartBase J α hs ht p u)) ≤ _ at hphys
      simp only [unitChartBase] at hphys
      rw [(extChartAt Model p).left_inv hx,(extChartAt Model p).left_inv humem.1,dist_eq_norm,norm_sub_rev] at hphys
      have htransport : dist x u.val.proj ≤ L*‖unitChartBase J α hs ht p u-extChartAt Model p x‖ :=
        hphys.trans (mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) (norm_nonneg _))
      have hdiv : dist x u.val.proj/(L*r) ≤ ‖unitChartBase J α hs ht p u-extChartAt Model p x‖/r := by
        apply (div_le_iff₀ hLr).mpr
        calc
          _ ≤ L*‖unitChartBase J α hs ht p u-extChartAt Model p x‖ := htransport
          _ = _ := by field_simp
      have hpro : ((1+‖unitChartBase J α hs ht p u-extChartAt Model p x‖/r)⁻¹)^6 ≤ P u := by
        exact pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) (by linarith)) 6
      calc
        _ ≤ radialCoefficient r ‖unitChartBase J α hs ht p u-extChartAt Model p x‖*
            ‖unitChartBase J α hs ht p u-extChartAt Model p x‖^2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2) (radialCoefficient_nonneg _ _)
        _ ≤ (8/r^2)*((1+‖unitChartBase J α hs ht p u-extChartAt Model p x‖/r)⁻¹)^6 :=
          radialCoefficient_quadratic_profile hr (norm_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hpro (by positivity)
    · rw [unitTransverseCut,indicator_of_notMem hu,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero]
      positivity
  have hi : Integrable (fun u => radialCoefficient r (unitDistanceCut J α hs ht p (extChartAt Model p x) K u)*
      ‖unitTransverseCut J α hs ht p (extChartAt Model p x) K u‖^2) μ := by
    apply (hpi.const_mul (8/r^2)).mono' (unitTransverse_rational_measurable J α hs ht p _ hK hKT r).aestronglyMeasurable
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (radialCoefficient_nonneg _ _) (sq_nonneg _))]
      exact hbound u
  refine ⟨hi,?_⟩
  have hg : ∀ s : ℝ, 0 < s → μ.real {u | ENNReal.ofReal (dist x u.val.proj) < ENNReal.ofReal s} ≤ M*s^2 := by
    intro s hsp
    simpa only [← edist_dist,geometric_edist_eq J α hs ht] using hgrowth x s hsp
  have hm : Measurable (fun u : MetricUnit (hermitianMetric J α hs ht) => ENNReal.ofReal (dist x u.val.proj)) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.dist hb)).measurable
  have hq := QuadraticShell.integral_profile_normalized_bound μ
    (fun u : MetricUnit (hermitianMetric J α hs ht) => ENNReal.ofReal (dist x u.val.proj)) hm M hM hg hLr
  have he (u : MetricUnit (hermitianMetric J α hs ht)) :
      (QuadraticShell.profile (L*r) (ENNReal.ofReal (dist x u.val.proj))).toReal = P u := by
    rw [QuadraticShell.profile_ofReal hLr dist_nonneg,ENNReal.toReal_ofReal (by positivity)]
  simp_rw [he] at hq
  have hqi := (div_le_iff₀ (sq_pos_of_pos hLr)).mp hq
  calc
    _ ≤ ∫ u, (8/r^2)*P u ∂μ := integral_mono hi (hpi.const_mul _) hbound
    _ = (8/r^2)*(∫ u, P u ∂μ) := integral_const_mul _ _
    _ ≤ (8/r^2)*(8*M*(L*r)^2) := mul_le_mul_of_nonneg_left hqi (by positivity)
    _ = _ := by field_simp; ring
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
