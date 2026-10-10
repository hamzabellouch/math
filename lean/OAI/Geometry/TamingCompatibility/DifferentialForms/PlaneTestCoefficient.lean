import Mathlib
import OAI.Geometry.TamingCompatibility.Currents.PlaneTest
import OAI.Geometry.TamingCompatibility.Functional.TestNorm
import OAI.Geometry.TamingCompatibility.Functional.CompactPairingBound

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory Hermitian Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
omit [CompactSpace X] in
lemma planeCurrentTest_coefficient_bound (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Space → ℝ, ∀ v : Space,
      ∀ hh : ContDiff ℝ ∞ h, ∀ hc : HasCompactSupport h,
      ∀ hK : tsupport h ⊆ (E p).concentrationCompact, ∀ x : X,
      ‖normalizedFrameEncode A J α ht E x
        ((planeCurrentTest p.val h v hh hc (hK.trans (E p).concentrationCompact_target)).val x)‖ ≤
        C*‖fderiv ℝ h (extChartAt Model p.val x)‖*‖v‖ := by
  obtain ⟨C,hC,hbound⟩ := normalizedFrameEncode_chart_bound A J α ht E hE p
  refine ⟨2*C,by positivity,fun h v hh hc hK x => ?_⟩
  by_cases hx : x ∈ (extChartAt Model p.val).symm '' (E p).concentrationCompact
  · obtain ⟨y,hy,rfl⟩ := hx
    have htgt := (E p).concentrationCompact_target hy
    have hb := hbound (planeCurrentTest p.val h v hh hc (hK.trans (E p).concentrationCompact_target)).val y hy
    change ‖normalizedFrameEncode A J α ht E _ _‖ ≤ C*‖ManifoldForms.pullback
      (exteriorDerivative (chartLift p.val (testOne h v))) (extChartAt Model p.val).symm y‖ at hb
    rw [pullback_exteriorDerivative_chartLift p.val (testOne_smooth hh v) (testOne_compact hc v)
      ((testOne_support h v).trans (hK.trans (E p).concentrationCompact_target)) htgt] at hb
    rw [(extChartAt Model p.val).right_inv htgt]
    exact hb.trans ((mul_le_mul_of_nonneg_left (testOne_deriv_norm
      (hh.differentiable (by simp)) v y) hC).trans_eq (by ring))
  · rw [planeCurrentTest_zero_off p.val h v hh hc (hK.trans (E p).concentrationCompact_target) hK hx]
    change ‖normalizedFrameEncode A J α ht E x (0 : MetricForms.Form Space 2)‖ ≤ _
    rw [map_zero,norm_zero]
    positivity

lemma reflected_fderiv_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : V → ℝ} (hh : Differentiable ℝ h) (b y : V) :
    ‖fderiv ℝ (fun z => h (b-z)) y‖ = ‖fderiv ℝ h (b-y)‖ := by
  have he : fderiv ℝ (fun z => h (b-z)) y = -fderiv ℝ h (b-y) := by
    ext w
    exact reflected_derivative hh b y w
  rw [he,norm_neg]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
