import OAI.Geometry.Relativity.CKS.ConstraintCanonical
import OAI.Geometry.Relativity.CKS.SourceExteriorDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildCKSAlgebra

namespace OAI

noncomputable section
namespace CKSSourceExterior
noncomputable section
open Set Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold CKSGeometricCuts
open CKSIntrinsicConstraints (ConstraintChart chart_exists_of_DECAt)
open scoped ContDiff Topology
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

lemma tensor_properties_from_representation
    (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N))
    (hKsym : ∀ x v w, K x v w = K x w v)
    (f : N → E) (A B : SpatialTensor) {x : N}
    (he : g.inner x = endInner I3 f A x ∧ K x = endInner I3 f B x) :
    (∀ v w, A (f x) v w = A (f x) w v) ∧
    (∀ v : E, v ≠ 0 → 0 < A (f x) v v) ∧
    (∀ v w, B (f x) v w = B (f x) w v) := by
  have hfull := endInner_fullRank g f A he.1
  refine ⟨?_,?_,?_⟩
  · intro v w
    obtain ⟨a,ha⟩ := hfull.2 v
    obtain ⟨b,hb⟩ := hfull.2 w
    have hs := g.symm x a b
    rw [he.1] at hs
    change A (f x) (mfderiv I3 𝓘(ℝ,E) f x a) (mfderiv I3 𝓘(ℝ,E) f x b) =
      A (f x) (mfderiv I3 𝓘(ℝ,E) f x b) (mfderiv I3 𝓘(ℝ,E) f x a) at hs
    simpa only [ha,hb] using hs
  · intro v hv
    obtain ⟨a,ha⟩ := hfull.2 v
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at ha
      change (0 : E) = v at ha
      exact hv ha.symm
    have hp := g.pos x a ha0
    rw [he.1] at hp
    change 0 < A (f x) (mfderiv I3 𝓘(ℝ,E) f x a) (mfderiv I3 𝓘(ℝ,E) f x a) at hp
    simpa only [ha] using hp
  · intro v w
    obtain ⟨a,ha⟩ := hfull.2 v
    obtain ⟨b,hb⟩ := hfull.2 w
    have hs := hKsym x a b
    rw [he.2] at hs
    change B (f x) (mfderiv I3 𝓘(ℝ,E) f x a) (mfderiv I3 𝓘(ℝ,E) f x b) =
      B (f x) (mfderiv I3 𝓘(ℝ,E) f x b) (mfderiv I3 𝓘(ℝ,E) f x a) at hs
    simpa only [ha,hb] using hs

lemma perturbation_symmetric_of_source {A : SpatialTensor} {y : E}
    (h : ∀ v w, sourceSpatial A y v w = sourceSpatial A y w v) :
    ∀ v w, A y v w = A y w v := by
  intro v w
  have hh : hyperbolicField y v w = hyperbolicField y w v := by
    rw [hyperbolicField_apply,hyperbolicField_apply]
    simp only [hyperbolicMetric,real_inner_comm v w]
    ring
  have hs := h v w
  change hyperbolicField y v w + A y v w = hyperbolicField y w v + A y w v at hs
  rw [hh] at hs
  exact add_left_cancel hs

lemma CKSData.source_geometry
    (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N))
    (hKsym : ∀ x v w, K x v w = K x w v)
    (hDEC : PhysicalDEC I3 g.inner K) (d : CKSData g K) :
    (∀ y, d.chart.radius < ‖y‖ → ∀ v w,
      d.metricPerturbation y v w = d.metricPerturbation y w v) ∧
    (∀ y, d.chart.radius < ‖y‖ → ∀ v w,
      d.tensorPerturbation y v w = d.tensorPerturbation y w v) ∧
    (∀ y, d.chart.radius < ‖y‖ → ∀ v : E, v ≠ 0 →
      0 < sourceSpatial d.metricPerturbation y v v) ∧
    (∀ y, d.chart.radius < ‖y‖ →
      spatialDEC (sourceSpatial d.metricPerturbation) (sourceSpatial d.tensorPerturbation) y) := by
  have hg (x : N) (hx : x ∈ d.chart.domain) :=
    tensor_properties_from_representation g K hKsym d.chart.coordinate
      (sourceSpatial d.metricPerturbation) (sourceSpatial d.tensorPerturbation) (d.represents x hx)
  have hy (y : E) (h : d.chart.radius < ‖y‖) := hg _ (d.chart.right_inverse y h).1
  have he (y : E) (h : d.chart.radius < ‖y‖) := (d.chart.right_inverse y h).2
  refine ⟨?_,?_,?_,?_⟩
  · intro y h
    apply perturbation_symmetric_of_source
    simpa only [he y h] using (hy y h).1
  · intro y h
    apply perturbation_symmetric_of_source
    simpa only [he y h] using (hy y h).2.2
  · intro y h
    simpa only [he y h] using (hy y h).2.1
  · intro y h
    let x := d.chart.inverse y
    have hx : x ∈ d.chart.domain := (d.chart.right_inverse y h).1
    let c : ConstraintChart g.inner K x := {
      domain := d.chart.domain
      coordinate := d.chart.coordinate
      metric := sourceSpatial d.metricPerturbation
      tensor := sourceSpatial d.tensorPerturbation
      isOpen := d.chart.isOpen
      mem := hx
      smooth := d.chart.smooth
      fullRank := fun z hz => endInner_fullRank g d.chart.coordinate _ (d.represents z hz).1
      coefficientSmooth := fun z hz =>
        ⟨sourceSpatial_smooth (d.metric_smooth _ (d.chart.mapsTo z hz)),
         sourceSpatial_smooth (d.tensor_smooth _ (d.chart.mapsTo z hz))⟩
      positiveSymmetric := hg
      represents := d.represents }
    obtain ⟨c₀,hc₀⟩ := chart_exists_of_DECAt (hDEC x)
    have heq := c₀.compare c
    rw [heq.1,heq.2] at hc₀
    change spatialDEC (sourceSpatial d.metricPerturbation) (sourceSpatial d.tensorPerturbation)
      (d.chart.coordinate x) at hc₀
    simpa only [x,he y h] using hc₀
end
end CKSSourceExterior

end

end OAI
