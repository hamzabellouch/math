import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.TransverseDefectCompare

namespace OAI

section

noncomputable section
private lemma lipschitzOn_norm_sub_fixed {V W : Type*} [NormedAddCommGroup V]
    [NormedAddCommGroup W] {f : V → W} {S : Set V} {L : NNReal}
    (hL : LipschitzOnWith L f S) {b y : V} (hb : b ∈ S) (hy : y ∈ S) :
    ‖f b-f y‖ ≤ (L:ℝ)*‖y-b‖ := by
  have hh := hL.dist_le_mul b hb y hy
  simpa only [dist_eq_norm,norm_sub_rev] using hh

namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory RadialPotential PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

lemma unitTransverse_local_bound (p : X) (b : Space) {R : ℝ} (hR : 0 < R)
    (hBT : Metric.closedBall b R ⊆ (extChartAt Model p).target) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ u ∈ unitChartDomain J α hs ht p (Metric.closedBall b R),
        ‖unitTransverse J α hs ht p b u‖^2 ≤
          C*unitRadialDefect J α hs ht p b u+B*‖unitChartBase J α hs ht p u-b‖^4 := by
  have hb := hBT (Metric.mem_closedBall_self hR.le)
  obtain ⟨m,hm,hml⟩ := unitChartVector_lower J α hs ht p (isCompact_closedBall b R) hBT
  obtain ⟨L,hL⟩ := ((coordinateJ_smooth J p).mono hBT).exists_lipschitzOnWith
    (by simp) (convex_closedBall b R) (isCompact_closedBall b R)
  let G := hermitianGraph (coordinateJ J p b)
  refine ⟨2/m^2,2*‖G‖^2*(L:ℝ)^2,by positivity,by positivity,fun u hu => ?_⟩
  have hu' := unitChart_mem J α hs ht p hBT hu
  have hcomp : ‖coordinateJ J p b-coordinateJ J p (unitChartBase J α hs ht p u)‖ ≤
      (L:ℝ)*‖unitChartBase J α hs ht p u-b‖ :=
    lipschitzOn_norm_sub_fixed hL (Metric.mem_closedBall_self hR.le) hu'.2
  exact transverse_graph_sq_bound _ _ (coordinateJ_square J p hb)
    (coordinateJ_square J p (hBT hu'.2)) _ _ (unitChartVector_ne_zero J α hs ht p u hu'.1)
    hm ((hml u hu).trans (hermitianGraph_norm_ge _ _)) L.coe_nonneg hcomp
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
