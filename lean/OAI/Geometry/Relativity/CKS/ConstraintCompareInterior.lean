import OAI.Geometry.Relativity.CKS.ConstraintCoordinateCovariance
import OAI.Geometry.Relativity.CKS.ConstraintInterior

namespace OAI

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing CKSAngularGeometry
open scoped ContDiff Topology
namespace CKSIntrinsicConstraints
lemma coordinateMomentumNorm_congr {A B C D : SpatialTensor} {x : E}
    (hA : A =ᶠ[𝓝 x] C) (hB : B =ᶠ[𝓝 x] D) :
    coordinateMomentumNorm A B x = coordinateMomentumNorm C D x := by
  unfold coordinateMomentumNorm
  rw [physicalMetricJet_congr (spatialCoefficients_congr hA),
    physicalTensorJet_congr (spatialCoefficients_congr hB)]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {g K : InnerField I (M := M)} {x : M}
lemma ConstraintChart.compare_interior (c d : ConstraintChart g K x)
    (hx : I.IsInteriorPoint x) : c.energy = d.energy ∧ c.momentumNorm = d.momentumNorm := by
  let u := extChartAt I x x
  have hu : u ∈ interior (extChartAt I x).target := I.isInteriorPoint_iff.mp hx
  have hux : (extChartAt I x).symm u = x := extChartAt_to_inv x
  have hcont : ContinuousAt (extChartAt I x).symm u :=
    ((contMDiffOn_extChartAt_symm (n := ∞) x u (interior_subset hu)).contMDiffAt
      (mem_interior_iff_mem_nhds.mp hu)).continuousAt
  have hc : (extChartAt I x).symm u ∈ c.domain := by rw [hux]; exact c.mem
  have hd : (extChartAt I x).symm u ∈ d.domain := by rw [hux]; exact d.mem
  have hnb : ∀ᶠ y in 𝓝 u, y ∈ interior (extChartAt I x).target ∧
      (extChartAt I x).symm y ∈ c.domain ∧ (extChartAt I x).symm y ∈ d.domain := by
    filter_upwards [isOpen_interior.mem_nhds hu,
      hcont.eventually (c.isOpen.mem_nhds hc),hcont.eventually (d.isOpen.mem_nhds hd)] with y hy hcy hdy
    exact ⟨hy,hcy,hdy⟩
  have hcov (a : ConstraintChart g K x) (ha : (extChartAt I x).symm u ∈ a.domain)
      (ah : ∀ᶠ y in 𝓝 u, (extChartAt I x).symm y ∈ a.domain) :=
    full_rank_spatial_constraints_pullback
      (show ∀ᶠ y in 𝓝 u, ContDiffAt ℝ ∞ (a.coordinate ∘ (extChartAt I x).symm) y from by
        filter_upwards [hnb,ah] with y hy hay
        exact a.interior_coordinate_smooth x hy.1 hay)
      (a.interior_coordinate_fullRank x hu ha)
      (show ∀ᶠ y in 𝓝 u, ContDiffAt ℝ ∞ a.metric (a.coordinate ((extChartAt I x).symm y)) ∧
        ContDiffAt ℝ ∞ a.tensor (a.coordinate ((extChartAt I x).symm y)) ∧
        (∀ v w, a.metric (a.coordinate ((extChartAt I x).symm y)) v w =
          a.metric (a.coordinate ((extChartAt I x).symm y)) w v) ∧
        (∀ v : E, v ≠ 0 → 0 < a.metric (a.coordinate ((extChartAt I x).symm y)) v v) from by
          filter_upwards [ah] with y hay
          exact ⟨(a.coefficientSmooth _ hay).1,(a.coefficientSmooth _ hay).2,
            (a.positiveSymmetric _ hay).1,(a.positiveSymmetric _ hay).2.1⟩)
      ((a.positiveSymmetric _ ha).2.2)
  have heq := hnb.mono (fun y hy => c.interior_pullback_equal d x hy.1 hy.2.1 hy.2.2)
  have hg := spatialEnergy_congr (heq.mono fun _ h => h.1) (heq.mono fun _ h => h.2)
  have hk := coordinateMomentumNorm_congr (heq.mono fun _ h => h.1) (heq.mono fun _ h => h.2)
  have hc' := hcov c hc (hnb.mono fun _ h => h.2.1)
  have hd' := hcov d hd (hnb.mono fun _ h => h.2.2)
  rw [hc'.1,hd'.1] at hg
  rw [hc'.2,hd'.2] at hk
  exact ⟨by simpa only [ConstraintChart.energy,Function.comp_apply,hux] using hg,
    by simpa only [ConstraintChart.momentumNorm,Function.comp_apply,hux] using hk⟩
end CKSIntrinsicConstraints

end

end OAI
