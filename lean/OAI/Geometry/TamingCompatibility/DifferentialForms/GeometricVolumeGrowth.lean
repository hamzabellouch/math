import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ScalarChartLift
import OAI.Geometry.TamingCompatibility.Hodge.HodgeManifoldPairingInitial

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization Set MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X)

include hs ht in
lemma volume_chart_closedBall_bound (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (D : ℝ) (hD : 0 ≤ D)
    (hDb : ∀ z ∈ L, chartDensity J α p z ≤ D)
    (b : Space) {s : ℝ} (hs0 : 0 < s) (hsub : Metric.closedBall b (2*s) ⊆ L) :
    (geometricVolume A J α).real ((extChartAt Model p).symm '' Metric.closedBall b s) ≤
      D*((2*s)^4*volume.real (Metric.closedBall (0:Space) 1)) := by
  classical
  let := geometricVolume_finite A J α hs ht
  let φ : ContDiffBump b := ⟨s,2*s,hs0,by linarith⟩
  have hφt : tsupport (φ : Space → ℝ) ⊆ (extChartAt Model p).target := by
    rw [φ.tsupport_eq]
    exact hsub.trans hLt
  let f : X → ℝ := scalarChartLift p φ
  have hf : Continuous f := (scalarChartLift_smooth p φ.contDiff φ.hasCompactSupport hφt).continuous
  have hf0 (x : X) : 0 ≤ f x := by
    by_cases hx : x ∈ (extChartAt Model p).source
    · simpa only [f,scalarChartLift,ite_eq_left hx] using φ.nonneg (x := extChartAt Model p x)
    · simp only [f,scalarChartLift,ite_eq_right hx,le_refl]
  have hfs : Function.support f ⊆ (extChartAt Model p).symm '' L := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := scalarChartLift_tsupport p φ.hasCompactSupport hφt (subset_tsupport f hx)
    exact ⟨z,hsub (by simpa only [φ.tsupport_eq] using hz),rfl⟩
  let G : Space → ℝ := (Metric.closedBall b (2*s)).indicator (fun _ => 1)
  have hGi : Integrable G := by
    exact (integrableOn_const (C := (1:ℝ))
      (hs := (isCompact_closedBall b (2*s)).measure_lt_top.ne)).integrable_indicator
        Metric.isClosed_closedBall.measurableSet
  have hG0 (z : Space) : 0 ≤ G z := by
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) z
  have hGf (z : Space) (hz : z ∈ (extChartAt Model p).target) : f ((extChartAt Model p).symm z) ≤ G z := by
    rw [show f ((extChartAt Model p).symm z) = φ z from scalarChartLift_apply_inverse p φ hz]
    by_cases hzb : z ∈ Metric.closedBall b (2*s)
    · simpa only [G,Set.indicator_of_mem hzb] using φ.le_one (x := z)
    · have hzφ : φ z = 0 := image_eq_zero_of_notMem_tsupport (by
        simpa only [φ.tsupport_eq] using hzb)
      simp only [G,Set.indicator_of_notMem hzb,hzφ,le_refl]
  have hub := integral_chart_bound J α hs ht A p L hL hLt D hD hDb f hf hf0 hfs G hGi hG0 hGf
  have hst : Metric.closedBall b s ⊆ (extChartAt Model p).target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans (hsub.trans hLt)
  have hK : IsCompact ((extChartAt Model p).symm '' Metric.closedBall b s) :=
    (isCompact_closedBall b s).image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hst)
  have hli : Integrable (((extChartAt Model p).symm '' Metric.closedBall b s).indicator (fun _ => (1:ℝ)))
      (geometricVolume A J α) := (integrable_const (1:ℝ)).indicator hK.measurableSet
  have hfi : Integrable f (geometricVolume A J α) := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hlb : (geometricVolume A J α).real ((extChartAt Model p).symm '' Metric.closedBall b s) ≤
      ∫ x, f x ∂geometricVolume A J α := by
    rw [← integral_indicator_one hK.measurableSet]
    apply integral_mono hli hfi
    intro x
    by_cases hx : x ∈ (extChartAt Model p).symm '' Metric.closedBall b s
    · rw [Set.indicator_of_mem hx]
      obtain ⟨z,hz,rfl⟩ := hx
      rw [show f ((extChartAt Model p).symm z) = φ z from scalarChartLift_apply_inverse p φ (hst hz)]
      exact (φ.one_of_mem_closedBall hz).ge
    · rw [Set.indicator_of_notMem hx]
      exact hf0 x
  have hG : (∫ z, G z) = (2*s)^4*volume.real (Metric.closedBall (0:Space) 1) := by
    change (∫ z, (Metric.closedBall b (2*s)).indicator (1 : Space → ℝ) z) = _
    rw [integral_indicator_one Metric.isClosed_closedBall.measurableSet,
      Measure.addHaar_real_closedBall' volume b (by positivity)]
    congr 1
    simp [Space]
  exact hlb.trans (by simpa only [hG] using hub)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
