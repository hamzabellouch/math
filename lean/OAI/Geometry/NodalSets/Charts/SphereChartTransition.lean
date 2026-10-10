import OAI.Geometry.NodalSets.Charts.SeedChartScalarExtension
import OAI.Geometry.NodalSets.Elliptic.JacobianCalculus

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def sphereChartCoordMap (p : Base) (x : Yau.Jets.Coord) : Base :=
  (extChartAt (𝓡 4) p).symm (seedCoordEquiv x)

def sphereChartTransitionDomain (p q : Base) : Set Yau.Jets.Coord :=
  sphereChartCoordMap p ⁻¹' (extChartAt (𝓡 4) q).source

def sphereChartTransition (p q : Base) (x : Yau.Jets.Coord) : Yau.Jets.Coord :=
  seedCoordEquiv.symm ((extChartAt (𝓡 4) q) (sphereChartCoordMap p x))

lemma sphereChartCoordMap_smooth (p : Base) : ContMDiff 𝓘(ℝ,Yau.Jets.Coord) (𝓡 4) ∞ (sphereChartCoordMap p) := by
  intro x
  exact (inverse_chart_smooth_at (I := 𝓡 4) p
    (y := seedCoordEquiv x) (by rw [centeredSphereChart_target]; trivial)).comp x
      seedCoordEquiv.contDiff.contMDiff.contMDiffAt

lemma sphereChartCoordMap_source (p : Base) (x : Yau.Jets.Coord) :
    sphereChartCoordMap p x ∈ (extChartAt (𝓡 4) p).source :=
  (extChartAt (𝓡 4) p).map_target (by rw [centeredSphereChart_target]; trivial)

lemma sphereChartTransitionDomain_open (p q : Base) : IsOpen (sphereChartTransitionDomain p q) :=
  (isOpen_extChartAt_source q).preimage (sphereChartCoordMap_smooth p).continuous

lemma sphereChartTransition_smoothOn (p q : Base) :
    ContDiffOn ℝ ∞ (sphereChartTransition p q) (sphereChartTransitionDomain p q) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  have hc := (contMDiffAt_extChartAt' (I := 𝓡 4) (x := q) (by simpa [sphereChartTransitionDomain] using hx)).comp x (sphereChartCoordMap_smooth p x)
  exact (seedCoordEquiv.symm.contDiff.contMDiff.contMDiffAt.comp x hc).contDiffAt

lemma sphereChartTransition_point (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    sphereChartCoordMap q (sphereChartTransition p q x) = sphereChartCoordMap p x := by
  unfold sphereChartCoordMap sphereChartTransition
  rw [seedCoordEquiv.apply_symm_apply]
  exact (extChartAt (𝓡 4) q).left_inv hx

lemma sphereChartTransition_mem (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    sphereChartTransition p q x ∈ sphereChartTransitionDomain q p := by
  change sphereChartCoordMap q (sphereChartTransition p q x) ∈ (extChartAt (𝓡 4) p).source
  rw [sphereChartTransition_point p q hx]
  exact sphereChartCoordMap_source p x

lemma sphereChartTransition_inverse (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    sphereChartTransition q p (sphereChartTransition p q x) = x := by
  rw [sphereChartTransition,sphereChartTransition_point p q hx]
  unfold sphereChartCoordMap
  rw [(extChartAt (𝓡 4) p).right_inv (by rw [centeredSphereChart_target]; trivial)]
  exact seedCoordEquiv.symm_apply_apply x

lemma sphereChartTransition_derivative_inverse (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    (fderiv ℝ (sphereChartTransition q p) (sphereChartTransition p q x)).comp
      (fderiv ℝ (sphereChartTransition p q) x) = ContinuousLinearMap.id ℝ Yau.Jets.Coord := by
  have hp := (sphereChartTransition_smoothOn p q).contDiffAt
    ((sphereChartTransitionDomain_open p q).mem_nhds hx)
  have hq := (sphereChartTransition_smoothOn q p).contDiffAt
    ((sphereChartTransitionDomain_open q p).mem_nhds (sphereChartTransition_mem p q hx))
  have he : (sphereChartTransition q p) ∘ (sphereChartTransition p q) =ᶠ[𝓝 x] id := by
    filter_upwards [(sphereChartTransitionDomain_open p q).mem_nhds hx] with y hy
    exact sphereChartTransition_inverse p q hy
  rw [← fderiv_comp x (hq.differentiableAt (by simp)) (hp.differentiableAt (by simp)),
    he.fderiv_eq,fderiv_id]

lemma sphereChartTransition_jacobian_ne_zero (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) : (jacobian (sphereChartTransition p q) x).det ≠ 0 := by
  have hleft := sphereChartTransition_derivative_inverse p q hx
  have hright := sphereChartTransition_derivative_inverse q p (sphereChartTransition_mem p q hx)
  rw [sphereChartTransition_inverse p q hx] at hright
  have hi : (fderiv ℝ (sphereChartTransition p q) x).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse hright hleft
  obtain ⟨e,he⟩ := hi
  change coordDet (fderiv ℝ (sphereChartTransition p q) x) ≠ 0
  rw [← he]
  exact coordDet_equiv_ne_zero e

end
end Yau.Target

end OAI
