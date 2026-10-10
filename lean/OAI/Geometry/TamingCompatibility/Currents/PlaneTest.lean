import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RationalKernelCompare
import OAI.Geometry.TamingCompatibility.Currents.PlaneMeasure

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory PlaneVariation Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

def planeCurrentTest (p : X) (h : Space → ℝ) (v : Space)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (hT : tsupport h ⊆ (extChartAt Model p).target) : smoothForms X 2 :=
  ⟨exteriorDerivative (chartLift p (testOne h v)),
    (chartLift_smooth p (testOne_smooth hh v) (testOne_compact hc v)
      ((testOne_support h v).trans hT)).exteriorDerivative⟩

omit [CompactSpace X] in
lemma planeCurrentTest_closed (p : X) (h : Space → ℝ) (v : Space)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (hT : tsupport h ⊆ (extChartAt Model p).target) :
    IsClosed (planeCurrentTest p h v hh hc hT).val :=
  (chartLift_smooth p (testOne_smooth hh v) (testOne_compact hc v)
    ((testOne_support h v).trans hT)).closed_exteriorDerivative

omit [CompactSpace X] in
lemma planeCurrentTest_zero_off (p : X) (h : Space → ℝ) (v : Space)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (hT : tsupport h ⊆ (extChartAt Model p).target)
    {K : Set Space} (hsK : tsupport h ⊆ K) {x : X}
    (hx : x ∉ (extChartAt Model p).symm '' K) :
    (planeCurrentTest p h v hh hc hT).val x = 0 := by
  apply exteriorDerivative_eq_zero_of_eventually
  have hxc : x ∉ liftSupport p (testOne h v) := by
    rintro ⟨z,hz,hzx⟩
    exact hx ⟨z,hsK (testOne_support h v hz),hzx⟩
  filter_upwards [(liftSupport_compact p (testOne_compact hc v)
    ((testOne_support h v).trans hT)).isClosed.isOpen_compl.mem_nhds hxc] with y hy
  exact chartLift_zero_off p (testOne h v) hy

omit [CompactSpace X] in
lemma planeCurrentTest_eval (p : X) (h : Space → ℝ) (v : Space)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (hT : tsupport h ⊆ (extChartAt Model p).target)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source) :
    unitEvaluation J (hermitianMetric J α hs ht)
      (planeCurrentTest p h v hh hc hT).val (planeCurrentTest p h v hh hc hT).property u =
      unitChartArea J α hs ht p u *
        fderiv ℝ h (unitChartBase J α hs ht p u)
          (skew (unitChartFirst J α hs ht p u) (unitChartSecond J α hs ht p u) v) := by
  have he := unitChartArea_eval J α hs ht p
    (planeCurrentTest p h v hh hc hT).val
    (show IsSmooth (planeCurrentTest p h v hh hc hT).val from
      (planeCurrentTest p h v hh hc hT).property) u hu
  apply he.trans
  change unitChartArea J α hs ht p u *
    ManifoldForms.pullback (exteriorDerivative (chartLift p (testOne h v)))
      (extChartAt Model p).symm (unitChartBase J α hs ht p u) _ = _
  simp only [unitChartBase]
  rw [pullback_exteriorDerivative_chartLift p (testOne_smooth hh v) (testOne_compact hc v)
      ((testOne_support h v).trans hT) ((extChartAt Model p).map_source hu),
    testOne_skew (hh.differentiable (by simp))]
  simp only [skew,real_inner_comm]

lemma planeCurrentTest_current (p : X) (h : Space → ℝ) (v : Space)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    {K : Set Space} (hKT : K ⊆ (extChartAt Model p).target) (hsK : tsupport h ⊆ K)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    unitMeasureCurrent J (hermitianMetric J α hs ht) μ (planeCurrentTest p h v hh hc (hsK.trans hKT)) =
      ∫ u, (unitChartDomain J α hs ht p K).indicator
        (fun u => unitChartArea J α hs ht p u *
          fderiv ℝ h (unitChartBase J α hs ht p u)
            (skew (unitChartFirst J α hs ht p u) (unitChartSecond J α hs ht p u) v)) u ∂μ := by
  apply integral_congr_ae
  apply ae_of_all
  intro u
  by_cases hu : u ∈ unitChartDomain J α hs ht p K
  · rw [indicator_of_mem hu]
    exact planeCurrentTest_eval J α hs ht p h v hh hc (hsK.trans hKT) u
      (unitChart_mem J α hs ht p hKT hu).1
  · rw [indicator_of_notMem hu]
    change ((planeCurrentTest p h v hh hc (hsK.trans hKT)).val u.val.proj) _ = 0
    rw [planeCurrentTest_zero_off p h v hh hc (hsK.trans hKT) hsK hu]
    rfl
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
