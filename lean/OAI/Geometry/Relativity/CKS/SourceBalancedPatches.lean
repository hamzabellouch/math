import OAI.Geometry.Relativity.CKS.SchwarzschildPosition
import OAI.Geometry.Relativity.CKS.SurfaceVolume

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

def SpatialBoostPatch.asCKS {e : ℝ} {p : E} {he : ‖p‖ < e}
    {A B : SpatialTensor} {Q : CKSTensorPatch} {P : SmoothAngularPatch}
    {θ : Angle} {δ R : ℝ} (h : SpatialBoostPatch e p he A B Q P θ δ R) : CKSTensorPatch where
  patch := P
  region := Metric.ball θ δ
  open_region := Metric.isOpen_ball
  region_target := h.genuine.estimates.ball_target
  radius := R
  metric := polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)
  second := polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) B)
  mr := lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr
  mg := lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg
  mK := lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK
  mr_smooth := h.genuine.estimates.radial_smooth
  mg_smooth := fun i k _ _ => h.genuine.estimates.angular_smooth i k
  mK_smooth := fun i k _ _ => h.genuine.estimates.second_smooth i k
  metric_CKS := h.metric_CKS
  second_CKS := h.second_CKS

lemma SpatialBoostPatch.asCKS_realizes {e : ℝ} {p : E} {he : ‖p‖ < e}
    {A B : SpatialTensor} {Q : CKSTensorPatch} {P : SmoothAngularPatch}
    {θ : Angle} {δ R : ℝ} (h : SpatialBoostPatch e p he A B Q P θ δ R) :
    h.asCKS.Realizes (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)
      (spatialTensorPullback (hyperbolicMap e (mass e p) p) B) := by
  intro y hy i k
  exact ⟨rfl,rfl⟩

lemma SpatialBoostPatch.asCKS_aspect {M : Sphere → ℝ} {e : ℝ} {p : E} {he : ‖p‖ < e}
    {A B : SpatialTensor} {Q : CKSTensorPatch} {P : SmoothAngularPatch}
    {θ : Angle} {δ R : ℝ} (h : SpatialBoostPatch e p he A B Q P θ δ R)
    (hrep : Q.RepresentsMassAspect M) : h.asCKS.RepresentsMassAspect (aspectPullback e p he M) := by
  intro n hn
  change n ∈ P.sphereRegion (Metric.ball θ δ) at hn
  have hm := genuine_patch_massAspect h.genuine hrep hn.2
  simpa only [SpatialBoostPatch.asCKS, P.chart.left_inv hn.1] using hm

lemma boosted_cks_patches {M : Sphere → ℝ} {e : ℝ} {p : E} (he : ‖p‖ < e)
    (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
    (hcovers : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hreal : ∀ n, (old n).Realizes A B) (hrep : ∀ n, (old n).RepresentsMassAspect M) :
    ∃ new : Sphere → CKSTensorPatch,
      (∀ n, n ∈ (new n).patch.sphereRegion (new n).region) ∧
      (∀ n, (new n).Realizes (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)
        (spatialTensorPullback (hyperbolicMap e (mass e p) p) B)) ∧
      (∀ n, (new n).RepresentsMassAspect (aspectPullback e p he M)) := by
  classical
  obtain ⟨s,P,δ,R,hR,hpatch,hcover⟩ :=
    exists_precompact_spatial_boost_atlas he A B old hcovers hreal
  choose index hmem hindex using hcover
  let H (n : Sphere) := hpatch (index n) (hmem n)
  refine ⟨fun n => (H n).asCKS,?_,?_,?_⟩
  · intro n
    refine ⟨(hindex n).1,?_⟩
    have hδ : δ (index n) ≤ 2*δ (index n) := by
      have hp := (H n).genuine.estimates.ball_pos
      linarith
    exact Metric.ball_subset_ball hδ (hindex n).2
  · intro n
    exact (H n).asCKS_realizes
  · intro n
    exact (H n).asCKS_aspect (hrep _)
end
end CKSLorentz

end

end OAI
