import Mathlib.MeasureTheory.Function.Jacobian
import OAI.Geometry.NodalSets.Charts.SphereTransitionFrame

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section
local instance sphereMeasureChartGeometryLocal1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

lemma centeredSphereChart_source (p : Base) :
    (extChartAt (𝓡 4) p).source = {-p}ᶜ := by
  rw [extChartAt_source]
  exact stereographic'_source (-p)

lemma sphereChartCoordMap_injective (p : Base) : Function.Injective (sphereChartCoordMap p) := by
  intro x y h
  have h' := congrArg (extChartAt (𝓡 4) p) h
  have hx : seedCoordEquiv x ∈ (extChartAt (𝓡 4) p).target := by rw [centeredSphereChart_target]; trivial
  have hy : seedCoordEquiv y ∈ (extChartAt (𝓡 4) p).target := by rw [centeredSphereChart_target]; trivial
  rw [sphereChartCoordMap,sphereChartCoordMap,(extChartAt (𝓡 4) p).right_inv hx,
    (extChartAt (𝓡 4) p).right_inv hy] at h'
  exact seedCoordEquiv.injective h'

lemma sphereChartTransitionDomain_ae (p q : Base) :
    ∀ᵐ x : Yau.Jets.Coord, x ∈ sphereChartTransitionDomain p q := by
  have hs : (sphereChartTransitionDomain p q)ᶜ = sphereChartCoordMap p ⁻¹' {-q} := by
    simp only [sphereChartTransitionDomain,centeredSphereChart_source,preimage_compl,compl_compl]
  apply (ae_iff).mpr
  change volume ((sphereChartTransitionDomain p q)ᶜ) = 0
  rw [hs]
  exact (Set.subsingleton_singleton.preimage (sphereChartCoordMap_injective p)).measure_zero volume

lemma sphereChartTransition_injOn (p q : Base) :
    InjOn (sphereChartTransition p q) (sphereChartTransitionDomain p q) := by
  intro x hx y hy h
  have he := congrArg (sphereChartTransition q p) h
  simpa only [sphereChartTransition_inverse p q hx,sphereChartTransition_inverse p q hy] using he

lemma sphereChartTransition_image_domain (p q : Base) :
    sphereChartTransition p q '' sphereChartTransitionDomain p q = sphereChartTransitionDomain q p := by
  apply Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact sphereChartTransition_mem p q hx
  · intro y hy
    exact ⟨sphereChartTransition q p y,sphereChartTransition_mem q p hy,
      sphereChartTransition_inverse q p hy⟩

lemma sphereChartTransition_hasFDeriv (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    HasFDerivAt (sphereChartTransition p q) (fderiv ℝ (sphereChartTransition p q) x) x :=
  ((sphereChartTransition_smoothOn p q).contDiffAt
    ((sphereChartTransitionDomain_open p q).mem_nhds hx)).differentiableAt (by simp) |>.hasFDerivAt

lemma jacobian_det_eq (f : Yau.Jets.Coord → Yau.Jets.Coord) (x : Yau.Jets.Coord) :
    (jacobian f x).det = (fderiv ℝ f x).det := by
  have he : jacobian f x = LinearMap.toMatrix (Pi.basisFun ℝ (Fin 4))
      (Pi.basisFun ℝ (Fin 4)) (fderiv ℝ f x).toLinearMap := by
    ext i j
    simp [jacobian]
  rw [he,LinearMap.det_toMatrix]

end
end Yau.Target

end OAI
