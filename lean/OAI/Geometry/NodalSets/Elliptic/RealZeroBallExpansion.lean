import OAI.Geometry.NodalSets.Elliptic.RealOneSidedPropagation
import OAI.Geometry.NodalSets.Elliptic.RealSphericalPhase

namespace OAI

namespace Yau.Geometry
open Metric Filter Set
open scoped ContDiff Topology
noncomputable section

theorem real_zero_germ_expands (gamma potential W : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hpot : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (hW : ContDiff ℝ ∞ W) (hpos : ∀ x, (B x).PosDef)
    (y : Yau.Jets.Coord) (R : ℝ) (hR : 0 < R)
    (hEq : ∀ x ∈ ball y R, realEllipticResidual gamma potential B W x = 0)
    (hy : W =ᶠ[𝓝 y] (fun _ ↦ 0)) : ∀ x ∈ ball y (R/4), W x = 0 := by
  intro x hx
  by_contra hxW
  let C := tsupport W ∩ closedBall y R
  have hCx : x ∈ C := ⟨subset_tsupport _ hxW,mem_closedBall.mpr
    ((mem_ball.mp hx).le.trans (by linarith))⟩
  have hCc : IsCompact C := (isCompact_closedBall y R).inter_left (isClosed_tsupport W)
  obtain ⟨z,hz,hmin⟩ := hCc.exists_isMinOn ⟨x,hCx⟩ (realCoordinateSquare_smooth y).continuous.continuousOn
  have hzx : realCoordinateSquare y z ≤ realCoordinateSquare y x := hmin hCx
  have hxupper : realCoordinateSquare y x ≤ 4*dist x y^2 := by
    simpa only [realCoordinateSquare,dist_eq_norm,Pi.sub_apply] using coord_sum_sq_le_four_norm_sq (x-y)
  have hzR2 : realCoordinateSquare y z < R^2 := by
    have hd := mem_ball.mp hx
    nlinarith only [hzx,hxupper,hd,dist_nonneg (x := x) (y := y),hR]
  have hzR : dist z y < R := by
    have hn := realCoordinateSquare_norm y z
    rw [← dist_eq_norm] at hn
    nlinarith only [hn,hzR2,dist_nonneg (x := z) (y := y),hR]
  have hzy : z ≠ y := by
    intro he; subst z
    exact (notMem_tsupport_iff_eventuallyEq.mpr hy) hz.1
  let psi := fun w ↦ realCoordinateSquare y z-realCoordinateSquare y w
  have hpsi : ContDiff ℝ ∞ psi := contDiff_const.sub (realCoordinateSquare_smooth y)
  have hpsi0 : psi z = 0 := sub_self _
  have hgrad : realCoordGradient psi z ≠ 0 := realSphericalPhase_gradient_ne_zero y z _ hzy
  have hside (w : Yau.Jets.Coord) (hp : 0 < psi w) : W w = 0 := by
    by_contra hn
    have hQ : realCoordinateSquare y w < realCoordinateSquare y z := sub_pos.mp hp
    have hwR : dist w y < R := by
      have hh := realCoordinateSquare_norm y w
      rw [← dist_eq_norm] at hh
      nlinarith only [hh,hQ,hzR2,dist_nonneg (x := w) (y := y),hR]
    exact (not_le_of_gt hQ) (hmin ⟨subset_tsupport _ hn,mem_closedBall.mpr hwR.le⟩)
  let delta := R-dist z y
  have hd : 0 < delta := sub_pos.mpr hzR
  have hsub : ball z delta ⊆ ball y R := by
    intro w hw
    have hh := dist_triangle w z y
    have hw' := mem_ball.mp hw
    apply mem_ball.mpr
    dsimp [delta] at hw'
    linarith
  obtain ⟨eps,heps,_,hzero⟩ := real_one_sided_strict_zero_propagation gamma potential psi W B
    hg hgp hpot hB hsym hpsi hW z delta hd hpsi0 hgrad (hpos z)
    (fun w hw ↦ hEq w (hsub hw)) (fun w _ hp ↦ hside w hp)
  have he : W =ᶠ[𝓝 z] (fun _ ↦ 0) := by
    filter_upwards [ball_mem_nhds z heps] with w hw
    exact hzero w hw
  exact (notMem_tsupport_iff_eventuallyEq.mpr he) hz.1

end
end Yau.Geometry

end OAI
