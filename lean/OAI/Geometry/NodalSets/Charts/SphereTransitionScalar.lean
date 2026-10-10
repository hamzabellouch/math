import OAI.Geometry.NodalSets.Charts.SeedChartOperator
import OAI.Geometry.NodalSets.Charts.SphereChartTransition

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def sphereScalarPartial (f : Base → ℝ) (p : Base) (i : Fin 4) (x : Coord) : ℝ :=
  fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) (seedCoordEquiv x)
    (EuclideanSpace.basisFun (Fin 4) ℝ i)

lemma sphereScalarPullback_smooth (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) :
    ContDiff ℝ ∞ (fun x ↦ (f (sphereChartCoordMap p x) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hf.comp (sphereChartCoordMap_smooth p)).contDiff

lemma sphereScalarPartial_eq (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) (i : Fin 4) (x : Coord) :
    (sphereScalarPartial f p i x : ℂ) =
      coordPartial i (fun y ↦ (f (sphereChartCoordMap p y) : ℂ)) x := by
  symm
  exact seedCoordPartial_pullback _ (fun z ↦
    (smooth_inverse_chart_comp f hf p (by rw [centeredSphereChart_target]; trivial)).differentiableAt
      (by simp)) i x

lemma sphereChartTransition_scalar (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p q : Base) {x : Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) (i : Fin 4) :
    sphereScalarPartial f p i x = ∑ j,
      jacobian (sphereChartTransition p q) x j i *
        sphereScalarPartial f q j (sphereChartTransition p q x) := by
  have he : (fun y ↦ (f (sphereChartCoordMap p y) : ℂ)) =ᶠ[𝓝 x]
      (fun y ↦ (f (sphereChartCoordMap q y) : ℂ)) ∘ sphereChartTransition p q := by
    filter_upwards [(sphereChartTransitionDomain_open p q).mem_nhds hx] with y hy
    simp only [Function.comp_apply,sphereChartTransition_point p q hy]
  have hF := (sphereChartTransition_smoothOn p q).contDiffAt
    ((sphereChartTransitionDomain_open p q).mem_nhds hx)
  have hd : coordPartial i (fun y ↦ (f (sphereChartCoordMap p y) : ℂ)) x =
      ∑ j, (jacobian (sphereChartTransition p q) x j i : ℂ) *
        coordPartial j (fun y ↦ (f (sphereChartCoordMap q y) : ℂ)) (sphereChartTransition p q x) := by
    unfold coordPartial
    rw [he.fderiv_eq]
    exact coordPartial_comp _ x (hF.differentiableAt (by simp)) _
      ((sphereScalarPullback_smooth f hf q).differentiable (by simp) _) i
  simp only [← sphereScalarPartial_eq f hf] at hd
  exact_mod_cast hd

end
end Yau.Target

end OAI
