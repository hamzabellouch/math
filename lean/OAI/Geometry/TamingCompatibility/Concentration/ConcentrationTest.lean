import Mathlib
import OAI.Geometry.TamingCompatibility.Currents.PlaneFirstVariation
import OAI.Geometry.TamingCompatibility.DifferentialForms.PlaneTestCoefficient
import OAI.Geometry.TamingCompatibility.DifferentialForms.CutGradientBound

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory Hermitian Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def concentrationTest (p : A.centers) (r : ℝ) (hr : 0 < r)
    (x : X) (hx : x ∈ tsupport (A.partition p)) (v : Space) : smoothForms X 2 :=
  planeCurrentTest p.val (fun y => cutKernel (E p).concentrationCutoff.bump r (extChartAt Model p.val x-y)) v
    (reflected_smooth _ (cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff) _)
    (reflected_compact _ (cutKernel_compact _ (E p).concentrationCutoff.bump.hasCompactSupport r) _)
    (((E p).concentrationCutoff.reflected_support (partition_center_ball A J α ht E hE p hx) r).trans
      (E p).concentrationCompact_target)

omit [CompactSpace X] [ConnectedSpace X] in
lemma concentrationTest_closed (p : A.centers) {r : ℝ} (hr : 0 < r)
    (x : X) (hx : x ∈ tsupport (A.partition p)) (v : Space) :
    IsClosed (concentrationTest A J α ht E hE p r hr x hx v).val :=
  planeCurrentTest_closed _ _ _ _ _ _

include hE in
lemma concentrationTest_coefficient_physical (p : A.centers) :
    ∃ B C L : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ 0 < L ∧
      ∀ r : ℝ, ∀ hr : 0 < r, ∀ x : X, ∀ hx : x ∈ tsupport (A.partition p),
      ∀ v : Space, ∀ y : X,
      ‖normalizedFrameEncode A J α ht E y
        ((concentrationTest A J α ht E hE p r hr x hx v).val y)‖ ≤
      ((B/r^3)*physicalProfile J α hs ht (L*r) x y+C*r^4)*‖v‖ := by
  obtain ⟨B,hB,hcoef⟩ := planeCurrentTest_coefficient_bound A J α ht E hE p
  obtain ⟨L,hL,hprofile⟩ := compact_chart_profile_bound_points J α hs ht p.val
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
  refine ⟨48*B,B*C,L,by positivity,by positivity,hL,fun r hr x hx v y => ?_⟩
  let h := fun z => cutKernel (E p).concentrationCutoff.bump r (extChartAt Model p.val x-z)
  have hK : tsupport h ⊆ (E p).concentrationCompact :=
    (E p).concentrationCutoff.reflected_support (partition_center_ball A J α ht E hE p hx) r
  by_cases hy : y ∈ (extChartAt Model p.val).symm '' (E p).concentrationCompact
  · have hysrc : y ∈ (extChartAt Model p.val).source := by
      obtain ⟨z,hz,rfl⟩ := hy
      exact (extChartAt Model p.val).map_target ((E p).concentrationCompact_target hz)
    have hyK : extChartAt Model p.val y ∈ (E p).concentrationCompact := by
      obtain ⟨z,hz,rfl⟩ := hy
      rwa [(extChartAt Model p.val).right_inv ((E p).concentrationCompact_target hz)]
    have hh := hcoef h v (reflected_smooth _ (cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff) _)
      (reflected_compact _ (cutKernel_compact _ (E p).concentrationCutoff.bump.hasCompactSupport r) _) hK y
    rw [reflected_fderiv_norm (cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff |>.differentiable (by simp))] at hh
    have hp := hprofile x y (A.subordinate p hx) hysrc
      ((E p).concentrationCompact_center (partition_center_ball A J α ht E hE p hx)) hyK r hr
    have hd := (hder r hr (extChartAt Model p.val x-extChartAt Model p.val y)).trans
      (add_le_add (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 48/r^3)) le_rfl)
    exact hh.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hB) (norm_nonneg v)).trans_eq (by ring))
  · change ‖normalizedFrameEncode A J α ht E y ((planeCurrentTest _ h v _ _ _).val y)‖ ≤ _
    rw [planeCurrentTest_zero_off p.val h v _ _ _ hK hy]
    change ‖normalizedFrameEncode A J α ht E y (0 : MetricForms.Form Space 2)‖ ≤ _
    rw [map_zero,norm_zero]
    exact mul_nonneg (add_nonneg (mul_nonneg (by positivity) (physicalProfile_nonneg J α hs ht _ _ _)) (by positivity)) (norm_nonneg _)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
