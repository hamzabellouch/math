import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ChartMetricBounds
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGeometricGarding
import OAI.Geometry.TamingCompatibility.Hodge.HodgeChartScalar
import OAI.Geometry.TamingCompatibility.Hodge.HodgeWedgeEnergy

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.ManifoldHodge
open Bundle ContinuousAlternatingMap ManifoldForms ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_codifferential (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a : TwoForm X} (ha : IsSmooth a)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z =
      -MetricHodge.starThree (coordinateMetric J α ht p z)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (extDeriv (ManifoldForms.pullback (starTwo J α ht a) (extChartAt Model p).symm) z) := by
  have hneg (b : ManifoldForms.Form X 1) :
      ManifoldForms.pullback (-b) (extChartAt Model p).symm z =
        -ManifoldForms.pullback b (extChartAt Model p).symm z := by ext v; rfl
  change ManifoldForms.pullback (-(starThree J α ht (exteriorDerivative (starTwo J α ht a))))
    (extChartAt Model p).symm z = _
  rw [hneg,pullback_starThree J α ht _ p hz,
    pullback_exteriorDerivative _ (starTwo_smooth J α hs ht ha)
      (isOpen_extChartAt_target p) (contMDiffOn_extChartAt_symm p) hz]
  congr 2
  exact extDerivWithin_eq_of_mem (isOpen_extChartAt_target p) hz

lemma pullback_codifferential_star (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a : TwoForm X} (ha : IsSmooth a)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (codifferential J α ht (starTwo J α ht a)) (extChartAt Model p).symm z =
      -MetricHodge.starThree (coordinateMetric J α ht p z)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (extDeriv (ManifoldForms.pullback a (extChartAt Model p).symm) z) := by
  rw [pullback_codifferential J α hs ht (starTwo_smooth J α hs ht ha) p hz,starTwo_square]
end TamingCompatibility.ManifoldHodge

namespace TamingCompatibility.HodgeChart
open GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume ContinuousAlternatingMap
open Set MeasureTheory
open scoped Manifold ContDiff SchwartzMap Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)

lemma cutoffDelta_zero_off (p : A.centers) (a : TwoForm X)
    {x : X} (hx : x ∉ tsupport (A.partition p)) :
    codifferential J α ht (cutoffForm A p a) x = 0 := by
  unfold codifferential
  change -(starThree J α ht (exteriorDerivative (starTwo J α ht (fun y => A.partition p y • a y))) x) = 0
  rw [hodgeStar_fun_smul]
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x) (invariantPart J α x)
    (exteriorDerivative (fun y => A.partition p y • starTwo J α ht a y) x) = 0
  rw [exteriorDerivative_fun_smul_vanishes _ hx]
  let F : MetricForms.Form Space 2 := invariantPart J α x
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x) F (0 : MetricForms.Form Space 3) = 0
  rw [MetricHodge.starThree_zero,neg_zero]

lemma cutoffDelta_pairing_tsupport (p : A.centers) (a : TwoForm X) :
    tsupport (GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
      (codifferential J α ht (cutoffForm A p a))) ⊆ tsupport (A.partition p) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  apply hx
  change MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
    (codifferential J α ht (cutoffForm A p a) x) (codifferential J α ht (cutoffForm A p a) x) = 0
  rw [cutoffDelta_zero_off A J α ht p a hn]
  exact (MetricForms.pairing_self_eq_zero _ _).mpr rfl

variable [CompactSpace X] (hs : IsSmooth α)
include hs in
lemma localDelta_density_integrable (p : A.centers) {a : TwoForm X} (ha : Smooth a) :
    Integrable (coordinateIntegrand J α p.val
      (GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
        (codifferential J α ht (cutoffForm A p a)))) := by
  apply coordinateIntegrand_integrable J α hs ht p.val
  · have hd := GeometricAdjoint.codifferential_smooth J α hs ht (cutoffForm_smooth A p ha)
    exact (GeometricAdjoint.pairing_one_smooth J α hs ht hd hd).continuous
  · exact (cutoffDelta_pairing_tsupport A J α ht p a).trans (A.subordinate p)

variable [MeasurableSpace X] [BorelSpace X]
include hs in
lemma integral_localDelta_density (p : A.centers) {a : TwoForm X} (ha : Smooth a) :
    (∫ z, coordinateIntegrand J α p.val
      (GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
        (codifferential J α ht (cutoffForm A p a))) z) =
    ∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
        (codifferential J α ht (cutoffForm A p a)) x ∂geometricVolume A J α := by
  have hd := GeometricAdjoint.codifferential_smooth J α hs ht (cutoffForm_smooth A p ha)
  rw [integral_geometricVolume_coordinate A J α hs ht p.val _
    (GeometricAdjoint.pairing_one_smooth J α hs ht hd hd).continuous
    ((cutoffDelta_pairing_tsupport A J α ht p a).trans (A.subordinate p)),
    ← integral_indicator (isOpen_extChartAt_target p.val).measurableSet]
  rfl
end TamingCompatibility.HodgeChart

end
end

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume GeometricChart
open Set MeasureTheory ContinuousAlternatingMap
open scoped Manifold ContDiff SchwartzMap Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def system (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) : Space → HodgeNormalSymbol.Q :=
  HodgeGeometricCoefficients.operator (coordinateMetric J α ht p.val) (coordinateJ J p.val)
    (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p.val).symm) (D p).frame
    (scalarSchwartz A J α ht D hD p a ha)

lemma field_eq (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) :
    HodgeGeometricCoefficients.field (coordinateMetric J α ht p.val) (D p).frame
      (scalarSchwartz A J α ht D hD p a ha) = localizedFunction A p a := by
  funext x
  exact (scalar_expansion A J α ht D hD p a x).symm

lemma starredField_local (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) {z : Space}
    (hz : z ∈ (extChartAt Model p.val).target) :
    HodgeGeometricCoefficients.starredField (coordinateMetric J α ht p.val) (coordinateJ J p.val)
      (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p.val).symm) (D p).frame
      (scalarSchwartz A J α ht D hD p a ha) z =
      ManifoldForms.pullback (starTwo J α ht (cutoffForm A p a)) (extChartAt Model p.val).symm z := by
  rw [HodgeGeometricCoefficients.starredField_eq,field_eq,
    localizedFunction_eq_cutoff A p a hz,pullback_starTwo J α ht _ p.val hz]

lemma system_zero_off (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) {z : Space}
    (hz : z ∉ coordinateSupport A p) : system A J α ht D hD p a ha z = 0 := by
  have hn (j : Fin 6) : z ∉ tsupport (scalarSchwartz A J α ht D hD p a ha j) :=
    fun h => hz (scalar_tsupport_subset A J α ht D p a j h)
  unfold system HodgeGeometricCoefficients.operator HodgeGeometricCoefficients.field
    HodgeGeometricCoefficients.starredField
  rw [HodgeGeometricCoefficients.extDeriv_sum_zero hn,HodgeGeometricCoefficients.extDeriv_sum_zero hn]
  simp only [MetricHodge.starThree_zero,_root_.map_zero,add_zero]

variable (hs : IsSmooth α)
include hs hD in
lemma system_energy (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) {z : Space}
    (hz : z ∈ coordinateSupport A p) :
    chartDensity J α p.val z * ‖system A J α ht D hD p a ha z‖^2 =
      coordinateIntegrand J α p.val (GeometricAdjoint.pairing J α ht
        (codifferential J α ht (cutoffForm A p a)) (codifferential J α ht (cutoffForm A p a))) z +
      coordinateIntegrand J α p.val (GeometricAdjoint.pairing J α ht
        (codifferential J α ht (cutoffForm A p (starTwo J α ht a)))
        (codifferential J α ht (cutoffForm A p (starTwo J α ht a)))) z := by
  have hzU := coordinateSupport_domain A J α ht D hD p hz
  have hzT := (D p).domain_subset hzU
  have hfield : localizedFunction A p a =ᶠ[𝓝 z]
      ManifoldForms.pullback (cutoffForm A p a) (extChartAt Model p.val).symm := by
    filter_upwards [(isOpen_extChartAt_target p.val).mem_nhds hzT] with y hy
    exact localizedFunction_eq_cutoff A p a hy
  have hstar : HodgeGeometricCoefficients.starredField (coordinateMetric J α ht p.val)
      (coordinateJ J p.val) (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p.val).symm)
      (D p).frame (scalarSchwartz A J α ht D hD p a ha) =ᶠ[𝓝 z]
      ManifoldForms.pullback (starTwo J α ht (cutoffForm A p a)) (extChartAt Model p.val).symm := by
    filter_upwards [(isOpen_extChartAt_target p.val).mem_nhds hzT] with y hy
    exact starredField_local A J α ht D hD p a ha hy
  have he₁ := pullback_codifferential J α hs ht (cutoffForm_smooth A p ha) p.val hzT
  have he₂ := pullback_codifferential_star J α hs ht (cutoffForm_smooth A p ha) p.val hzT
  have hcut : starTwo J α ht (cutoffForm A p a) = cutoffForm A p (starTwo J α ht a) :=
    hodgeStar_fun_smul J α ht (A.partition p) a
  rw [hcut] at he₂
  unfold system HodgeGeometricCoefficients.operator
  rw [field_eq,hstar.extDeriv_eq,hfield.extDeriv_eq,
    HodgeNormalOperator.output_norm _ _ ((D p).frame_gram z hzU)]
  rw [← neg_neg (MetricHodge.starThree _ _ (extDeriv _ z)),← he₁,
    MetricForms.pairing_neg_self]
  rw [← neg_neg (MetricHodge.starThree _ _ (extDeriv _ z)),← he₂,
    MetricForms.pairing_neg_self]
  rw [pairing_chart J α ht p.val (Or.inl rfl) _ _ hzT,
    pairing_chart J α ht p.val (Or.inl rfl) _ _ hzT]
  unfold coordinateIntegrand
  rw [indicator_of_mem hzT,indicator_of_mem hzT,mul_add]

include hs hD in
lemma system_norm_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, ∀ ha : IsSmooth a, ∀ z,
      ‖system A J α ht D hD p a ha z‖^2 ≤ C *
      (coordinateIntegrand J α p.val (GeometricAdjoint.pairing J α ht
        (codifferential J α ht (cutoffForm A p a)) (codifferential J α ht (cutoffForm A p a))) z +
      coordinateIntegrand J α p.val (GeometricAdjoint.pairing J α ht
        (codifferential J α ht (cutoffForm A p (starTwo J α ht a)))
        (codifferential J α ht (cutoffForm A p (starTwo J α ht a)))) z) := by
  obtain ⟨C,hC,hbound⟩ := density_lower_on_support A J α hs ht D hD p
  refine ⟨C,hC,?_⟩
  intro a ha z
  by_cases hz : z ∈ coordinateSupport A p
  · rw [← system_energy A J α ht D hD hs p a ha hz]
    have hh := mul_le_mul_of_nonneg_right (hbound z hz) (sq_nonneg ‖system A J α ht D hD p a ha z‖)
    nlinarith
  · rw [system_zero_off A J α ht D hD p a ha hz,norm_zero,zero_pow (by decide : 2≠0)]
    exact mul_nonneg hC.le (add_nonneg
      (coordinateIntegrand_self_nonneg J α ht p.val _ z)
      (coordinateIntegrand_self_nonneg J α ht p.val _ z))

variable [MeasurableSpace X] [BorelSpace X]
include hs hD in
lemma integral_system_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, ∀ ha : IsSmooth a,
      (∫ z, ‖system A J α ht D hD p a ha z‖^2) ≤ C *
      (∫ x, GeometricAdjoint.pairing J α ht
        (codifferential J α ht (cutoffForm A p a)) (codifferential J α ht (cutoffForm A p a)) x +
      GeometricAdjoint.pairing J α ht
        (codifferential J α ht (starTwo J α ht (cutoffForm A p a)))
        (codifferential J α ht (starTwo J α ht (cutoffForm A p a))) x ∂geometricVolume A J α) := by
  obtain ⟨C,hC,hbound⟩ := system_norm_bound A J α ht D hD hs p
  refine ⟨C,hC,?_⟩
  intro a ha
  have hi₁ := localDelta_density_integrable A J α ht hs p ha
  have hi₂ := localDelta_density_integrable A J α ht hs p (starTwo_smooth J α hs ht ha)
  have hh := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => sq_nonneg
    ‖system A J α ht D hD p a ha z‖)) ((hi₁.add hi₂).const_mul C)
    (Filter.Eventually.of_forall (hbound a ha))
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul,integral_add hi₁ hi₂,
    integral_localDelta_density A J α ht hs p ha,
    integral_localDelta_density A J α ht hs p (starTwo_smooth J α hs ht ha)] at hh
  have hcut : starTwo J α ht (cutoffForm A p a) = cutoffForm A p (starTwo J α ht a) :=
    hodgeStar_fun_smul J α ht (A.partition p) a
  rw [hcut]
  let := geometricVolume_finite A J α hs ht
  have hd₁ := GeometricAdjoint.codifferential_smooth J α hs ht (cutoffForm_smooth A p ha)
  have hd₂ := GeometricAdjoint.codifferential_smooth J α hs ht
    (cutoffForm_smooth A p (starTwo_smooth J α hs ht ha))
  rw [integral_add
    ((GeometricAdjoint.pairing_one_smooth J α hs ht hd₁ hd₁).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((GeometricAdjoint.pairing_one_smooth J α hs ht hd₂ hd₂).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  exact hh
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
