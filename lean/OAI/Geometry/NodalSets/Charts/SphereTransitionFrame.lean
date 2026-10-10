import OAI.Geometry.NodalSets.Charts.ChartFrameSmooth
import OAI.Geometry.NodalSets.Charts.SeedChartPrincipal
import OAI.Geometry.NodalSets.Charts.SphereChartTransition

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Matrix Set Filter
open scoped ContDiff Topology
noncomputable section
local instance sphereTransitionFrameDim : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

lemma sphereChartCoordMap_ambient_derivative (p : Base) (x : Yau.Jets.Coord) :
    fderiv ℝ (fun y ↦ (sphereChartCoordMap p y : AmbientBase)) x =
      (sphereChartDerivative p (seedCoordEquiv x)).comp seedCoordEquiv.toContinuousLinearMap := by
  change fderiv ℝ (((Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm) ∘ seedCoordEquiv) x = _
  rw [seedCoordEquiv.comp_right_fderiv,
    sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial)]

lemma sphereChartTransition_frame_derivative (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) (v : Yau.Jets.Coord) :
    sphereChartDerivative q (seedCoordEquiv (sphereChartTransition p q x))
      (seedCoordEquiv (fderiv ℝ (sphereChartTransition p q) x v)) =
      sphereChartDerivative p (seedCoordEquiv x) (seedCoordEquiv v) := by
  have hq : ContDiff ℝ ∞ (fun y ↦ (sphereChartCoordMap q y : AmbientBase)) :=
    ((contMDiff_coe_sphere (n := 4)).comp (sphereChartCoordMap_smooth q)).contDiff
  have hF := (sphereChartTransition_smoothOn p q).contDiffAt
    ((sphereChartTransitionDomain_open p q).mem_nhds hx)
  have he : (fun y ↦ (sphereChartCoordMap q y : AmbientBase)) ∘ sphereChartTransition p q =ᶠ[𝓝 x]
      (fun y ↦ (sphereChartCoordMap p y : AmbientBase)) := by
    filter_upwards [(sphereChartTransitionDomain_open p q).mem_nhds hx] with y hy
    exact congrArg (Subtype.val : Base → AmbientBase) (sphereChartTransition_point p q hy)
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp x (hq.differentiable (by simp) _) (hF.differentiableAt (by simp)),
    sphereChartCoordMap_ambient_derivative,sphereChartCoordMap_ambient_derivative] at hd
  exact congrArg (fun L : Yau.Jets.Coord →L[ℝ] AmbientBase ↦ L v) hd

lemma sphereChartTransition_frame (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    sphereChartFrame p (seedCoordEquiv x) =
      sphereChartFrame q (seedCoordEquiv (sphereChartTransition p q x)) * jacobian (sphereChartTransition p q) x := by
  ext i j
  have h := congrArg (fun v : AmbientBase ↦ v i)
    (sphereChartTransition_frame_derivative p q hx (Pi.single j 1))
  rw [seedCoordEquiv_basis] at h
  have hm := sphereChartFrame_mulVec q (seedCoordEquiv (sphereChartTransition p q x))
    (fderiv ℝ (sphereChartTransition p q) x (Pi.single j 1))
  have hm' := congrFun hm i
  change _ = (sphereChartDerivative q (seedCoordEquiv (sphereChartTransition p q x))
    (seedCoordEquiv (fderiv ℝ (sphereChartTransition p q) x (Pi.single j 1)))) i at hm'
  rw [sphereChartFrame_apply]
  exact h.symm.trans hm'.symm

lemma sphereChartTransition_round_matrix (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    sphereRoundChartMatrix p (seedCoordEquiv x) =
      (jacobian (sphereChartTransition p q) x).transpose *
        sphereRoundChartMatrix q (seedCoordEquiv (sphereChartTransition p q x)) *
          jacobian (sphereChartTransition p q) x := by
  simp only [sphereRoundChartMatrix,sphereChartTransition_frame p q hx,transpose_mul,Matrix.mul_assoc]

lemma sphereChartTransition_round_density (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    roundChartDensity p (seedCoordEquiv x) =
      |(jacobian (sphereChartTransition p q) x).det| *
        roundChartDensity q (seedCoordEquiv (sphereChartTransition p q x)) := by
  have hd : (sphereRoundChartMatrix p (seedCoordEquiv x)).det =
      (jacobian (sphereChartTransition p q) x).det^2 *
        (sphereRoundChartMatrix q (seedCoordEquiv (sphereChartTransition p q x))).det := by
    rw [sphereChartTransition_round_matrix p q hx]
    simp only [det_mul,det_transpose]
    ring
  unfold roundChartDensity
  rw [hd,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]

end
end Yau.Target

end OAI
