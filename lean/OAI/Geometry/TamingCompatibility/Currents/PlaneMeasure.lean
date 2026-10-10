import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FourthMomentKernel
import OAI.Geometry.TamingCompatibility.DifferentialForms.EuclideanUnitPlanes

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

def planeAreaCut (p : X) (K : Set Space) : MetricUnit (hermitianMetric J α hs ht) → ℝ :=
  (unitChartDomain J α hs ht p K).indicator (unitChartArea J α hs ht p)

def planeBaseCut (p : X) (K : Set Space) : MetricUnit (hermitianMetric J α hs ht) → Space :=
  (unitChartDomain J α hs ht p K).indicator (unitChartBase J α hs ht p)

omit [CompactSpace X] in
lemma planeBaseCut_measurable (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) : Measurable (planeBaseCut J α hs ht p K) := by
  classical
  exact (unitChartBase_continuousOn J α hs ht p hKT).measurable_piecewise continuousOn_const
    (unitChartDomain_closed J α hs ht p hK hKT).measurableSet

omit [CompactSpace X] in
lemma planeAreaCut_measurable (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) : Measurable (planeAreaCut J α hs ht p K) := by
  classical
  exact (unitChartArea_continuousOn J α hs ht p hKT).measurable_piecewise continuousOn_const
    (unitChartDomain_closed J α hs ht p hK hKT).measurableSet

omit [CompactSpace X] [T2Space X] in
lemma planeAreaCut_nonneg (p : X) (K : Set Space) (u : MetricUnit (hermitianMetric J α hs ht)) :
    0 ≤ planeAreaCut J α hs ht p K u := by
  apply indicator_nonneg _ u
  intro v _
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

lemma planeAreaCut_integrable (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    Integrable (planeAreaCut J α hs ht p K) μ := by
  obtain ⟨m,C,_,hC,hbound⟩ := unitChartArea_bounds J α hs ht p hK hKT
  apply (integrable_const C).mono' (planeAreaCut_measurable J α hs ht p hK hKT).aestronglyMeasurable
  apply ae_of_all
  intro u
  rw [Real.norm_eq_abs,abs_of_nonneg (planeAreaCut_nonneg J α hs ht p K u)]
  by_cases hu : u ∈ unitChartDomain J α hs ht p K
  · exact (indicator_of_mem hu _).le.trans (hbound u hu).2
  · rw [planeAreaCut,indicator_of_notMem hu]
    exact hC.le

def planeMeasure (p : X) (K : Set Space)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) : Measure Space :=
  (μ.withDensity (fun u => ENNReal.ofReal (planeAreaCut J α hs ht p K u))).map
    (planeBaseCut J α hs ht p K)

lemma planeMeasure_finite (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    IsFiniteMeasure (planeMeasure J α hs ht p K μ) := by
  have hi := planeAreaCut_integrable J α hs ht p hK hKT μ
  have hp := planeAreaCut_nonneg J α hs ht p K
  have hh : ∫⁻ u, ENNReal.ofReal (planeAreaCut J α hs ht p K u) ∂μ ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hp)]
    exact ENNReal.ofReal_ne_top
  let := isFiniteMeasure_withDensity hh
  exact inferInstanceAs (IsFiniteMeasure (Measure.map _ (μ.withDensity _)))

omit [CompactSpace X] in
lemma planeMeasure_integral (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (f : Space → W) (hf : Continuous f) :
    (∫ y, f y ∂planeMeasure J α hs ht p K μ) =
      ∫ u, (unitChartDomain J α hs ht p K).indicator
        (fun u => unitChartArea J α hs ht p u • f (unitChartBase J α hs ht p u)) u ∂μ := by
  rw [planeMeasure,integral_map (planeBaseCut_measurable J α hs ht p hK hKT).aemeasurable
    hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun u => ENNReal.ofReal (planeAreaCut J α hs ht p K u)) from
        ENNReal.measurable_ofReal.comp (planeAreaCut_measurable J α hs ht p hK hKT))
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  dsimp only
  rw [ENNReal.toReal_ofReal (planeAreaCut_nonneg J α hs ht p K u)]
  by_cases hu : u ∈ unitChartDomain J α hs ht p K
  · simp only [planeAreaCut,planeBaseCut,indicator_of_mem hu]
  · simp only [planeAreaCut,indicator_of_notMem hu,zero_smul]
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]

lemma pullback_exteriorDerivative_chartLift {k : ℕ} (p : X)
    {β : Space → Space [⋀^Fin k]→L[ℝ] ℝ}
    (hs : ContDiff ℝ ∞ β) (hc : HasCompactSupport β)
    (hβ : tsupport β ⊆ (extChartAt Model p).target)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    pullback (exteriorDerivative (chartLift p β)) (extChartAt Model p).symm z = extDeriv β z := by
  rw [pullback_exteriorDerivative _ (chartLift_smooth p hs hc hβ)
    (isOpen_extChartAt_target p) (contMDiffOn_extChartAt_symm p) hz,
    extDerivWithin_eq_of_mem (isOpen_extChartAt_target p) hz]
  apply Filter.EventuallyEq.extDeriv_eq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with y hy
  exact pullback_chartLift p β hy

end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.Concentration
open ContinuousAlternatingMap ExteriorForms
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def testOne (h : V → ℝ) (v : V) : V → V [⋀^Fin 1]→L[ℝ] ℝ :=
  fun y => h y • ofSubsingletonLIE (0 : Fin 1) (innerSL ℝ v)

lemma testOne_smooth {h : V → ℝ} (hh : ContDiff ℝ ∞ h) (v : V) :
    ContDiff ℝ ∞ (testOne h v) := hh.smul contDiff_const

lemma testOne_compact {h : V → ℝ} (hh : HasCompactSupport h) (v : V) :
    HasCompactSupport (testOne h v) := hh.smul_right

lemma testOne_support (h : V → ℝ) (v : V) : tsupport (testOne h v) ⊆ tsupport h :=
  tsupport_smul_subset_left _ _

lemma testOne_deriv {h : V → ℝ} (hh : Differentiable ℝ h) (v y a b : V) :
    extDeriv (testOne h v) y ![a,b] =
      (fderiv ℝ h y a)*⟪v,b⟫-(fderiv ℝ h y b)*⟪v,a⟫ := by
  unfold testOne
  rw [extDeriv_variable_smul (hh y) (differentiableAt_const _)]
  have hz : extDeriv (fun _ : V => ofSubsingletonLIE (0 : Fin 1) (innerSL ℝ v)) y = 0 := by
    rw [extDeriv,fderiv_fun_const]
    change alternatizeUncurryFinCLM ℝ V ℝ 0 = 0
    exact map_zero _
  rw [hz,smul_zero,zero_add,wedgeOne_apply_two]
  rfl

lemma testOne_skew {h : V → ℝ} (hh : Differentiable ℝ h) (v y a b : V) :
    extDeriv (testOne h v) y ![a,b] =
      fderiv ℝ h y (⟪v,b⟫ • a - ⟪v,a⟫ • b) := by
  rw [testOne_deriv hh,map_sub,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
  ring
end TamingCompatibility.Concentration

end
end

end OAI
