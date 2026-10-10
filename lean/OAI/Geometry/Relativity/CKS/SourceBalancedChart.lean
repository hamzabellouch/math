import OAI.Geometry.Relativity.CKS.SourceExteriorDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildCKSAlgebra
import OAI.Geometry.Relativity.CKS.SourceBalancedPatches

namespace OAI

noncomputable section
namespace CKSSourceExterior
noncomputable section
open Set Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold CKSGeometricCuts
open CKSSphericalHarmonics (SmoothSphere)
open scoped ContDiff Topology
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

lemma CKSData.balanced_in_chart
    (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N)) (d : CKSData g K)
    (ht : ‖(bondiCharge d.massAspect).2‖ < (bondiCharge d.massAspect).1)
    (c : CoordinateEnd (N := N)) (hdom : c.domain ⊆ d.chart.domain)
    (hcoord : c.coordinate = (hyperbolicHomeomorph (bondiCharge d.massAspect).1
      (bondiCharge d.massAspect).2 ht).symm ∘ d.chart.coordinate) :
    ∃ d' : CKSData g K, d'.chart = c ∧
      d'.massAspect = aspectPullback (bondiCharge d.massAspect).1 (bondiCharge d.massAspect).2 ht d.massAspect ∧
      bondiCharge d'.massAspect = (mass (bondiCharge d.massAspect).1 (bondiCharge d.massAspect).2,0) := by
  let e := (bondiCharge d.massAspect).1
  let p := (bondiCharge d.massAspect).2
  let H := hyperbolicHomeomorph e p ht
  let A' := spatialTensorPullback (hyperbolicMap e (mass e p) p) d.metricPerturbation
  let B' := spatialTensorPullback (hyperbolicMap e (mass e p) p) d.tensorPerturbation
  have hfar (y : E) (hy : c.radius < ‖y‖) : d.chart.radius < ‖H y‖ := by
    have hx := (c.right_inverse y hy).1
    have hr := (c.right_inverse y hy).2
    have he : d.chart.coordinate (c.inverse y) = H y := by
      rw [hcoord] at hr
      change H.symm (d.chart.coordinate (c.inverse y)) = y at hr
      simpa only [H.apply_symm_apply] using congrArg H hr
    rw [← he]
    exact d.chart.mapsTo _ (hdom hx)
  have hAs (y : E) (hy : c.radius < ‖y‖) : ContDiffAt ℝ ∞ A' y :=
    spatialTensorPullback_smooth (hyperbolicMap_smooth e (mass e p) p).contDiffAt
      (d.metric_smooth _ (hfar y hy))
  have hBs (y : E) (hy : c.radius < ‖y‖) : ContDiffAt ℝ ∞ B' y :=
    spatialTensorPullback_smooth (hyperbolicMap_smooth e (mass e p) p).contDiffAt
      (d.tensor_smooth _ (hfar y hy))
  obtain ⟨patches,hcover,hreal,hrep⟩ := boosted_cks_patches ht d.metricPerturbation
    d.tensorPerturbation d.patches d.covers d.realizes d.aspect_eq
  obtain ⟨hM',hcharge,_,_⟩ := balanced_charge_and_heat d.aspect_smooth ht
  let d' : CKSData g K := {
    chart := c
    metricPerturbation := A'
    tensorPerturbation := B'
    metric_smooth := hAs
    tensor_smooth := hBs
    represents := by
      intro x hx
      have hsx := d.chart.smooth.contMDiffAt (d.chart.isOpen.mem_nhds (hdom hx))
      rw [hcoord]
      exact ⟨(d.represents x (hdom hx)).1.trans
          (endInner_balanced ht d.chart.coordinate d.metricPerturbation hsx).symm,
        (d.represents x (hdom hx)).2.trans
          (endInner_balanced ht d.chart.coordinate d.tensorPerturbation hsx).symm⟩
    massAspect := aspectPullback e p ht d.massAspect
    aspect_smooth := hM'
    patches := patches
    covers := hcover
    realizes := hreal
    aspect_eq := hrep }
  exact ⟨d',rfl,rfl,hcharge⟩
end
end CKSSourceExterior

end

end OAI
