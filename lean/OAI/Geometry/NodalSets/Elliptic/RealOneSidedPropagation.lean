import OAI.Geometry.NodalSets.Coefficients.RealCutoffResidual
import OAI.Geometry.NodalSets.Elliptic.CompactSmoothExtension
import OAI.Geometry.NodalSets.Elliptic.RealCarlemanSupport
import OAI.Geometry.NodalSets.Elliptic.RealConvexifiedQuadraticLemmas

namespace OAI

namespace Yau.Geometry
open Metric Filter
open scoped ContDiff Topology
noncomputable section

theorem real_one_sided_strict_zero_propagation (gamma potential psi W : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hpot : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (hpsi : ContDiff ℝ ∞ psi) (hW : ContDiff ℝ ∞ W)
    (x0 : Yau.Jets.Coord) (R : ℝ) (hR : 0 < R)
    (hzero : psi x0 = 0) (hgrad : realCoordGradient psi x0 ≠ 0) (hpos : (B x0).PosDef)
    (hEq : ∀ x ∈ ball x0 R, realEllipticResidual gamma potential B W x = 0)
    (hside : ∀ x ∈ ball x0 R, 0 < psi x → W x = 0) :
    ∃ eps > 0, eps ≤ R ∧ ∀ x ∈ ball x0 eps, W x = 0 := by
  let psi0 := realIndentedPhase psi x0
  have hpsi0 : ContDiff ℝ ∞ psi0 := realIndentedPhase_smooth psi hpsi x0
  have hz0 : psi0 x0 = 0 := (realIndentedPhase_center psi x0).trans hzero
  have hg0 : realCoordGradient psi0 x0 ≠ 0 := by
    rw [realIndentedPhase_gradient_center psi hpsi]; exact hgrad
  obtain ⟨K,hK,r,hr,hcar⟩ := real_local_carleman_support gamma potential psi0 B hg hgp hpot
    hB hsym hpsi0 x0 hz0 hg0 hpos
  let phi := realConvexifiedPhase psi0 K
  have hphi : ContDiff ℝ ∞ phi := realConvexifiedPhase_smooth psi0 hpsi0 K
  have hphiz : phi x0 = 0 := by simp [phi,realConvexifiedPhase,hz0]
  have hlow0 : -(1/(2*K)) < psi0 x0 := by rw [hz0]; exact neg_neg_of_pos (by positivity)
  obtain ⟨r0,hr0,hnear⟩ := Metric.isOpen_iff.mp
    (isOpen_lt continuous_const hpsi0.continuous) x0 hlow0
  let s := min R (min r r0)/4
  have hs : 0 < s := by dsimp [s]; positivity
  have hsR : 2*s < R := by
    have hh := min_le_left R (min r r0); dsimp [s]; linarith
  have hsr : 2*s < r := by
    have hh := (min_le_right R (min r r0)).trans (min_le_left r r0); dsimp [s]; linarith
  have hsr0 : 2*s < r0 := by
    have hh := (min_le_right R (min r r0)).trans (min_le_right r r0); dsimp [s]; linarith
  obtain ⟨eta,heta,hetac,hetas,hetar,heta1⟩ := compact_smooth_cutoff
    (isCompact_closedBall x0 s) isOpen_ball
    (closedBall_subset_ball (by linarith : s < 2*s))
  let f := fun x ↦ eta x*W x
  have hf : ContDiff ℝ ∞ f := heta.mul hW
  have hfc : HasCompactSupport f := hetac.mul_right
  have hfs : tsupport f ⊆ ball x0 r :=
    tsupport_mul_subset_left.trans (hetas.trans (ball_subset_ball hsr.le))
  have hres (x) (hx : realEllipticResidual gamma potential B f x ≠ 0) : phi x ≤ -s^2/2 := by
    have hxeta : x ∈ tsupport eta := tsupport_mul_subset_left
      (realEllipticResidual_tsupport gamma potential B f (subset_tsupport _ hx))
    have hx2 := hetas hxeta
    obtain ⟨hxR,hd,hps⟩ := real_cutoff_residual_location gamma potential eta W psi B hpsi.continuous
      x0 R s (hetas.trans (ball_subset_ball hsR.le)) heta1 hEq hside x hx
    have hupper : psi0 x ≤ -s^2 := realIndentedPhase_annulus psi x0 x s hs.le hd hps
    have hlower : -(1/(2*K)) < psi0 x := hnear (ball_subset_ball hsr0.le hx2)
    have hh := realConvexifiedPhase_negative_bound psi0 K hK x hlower
      (hupper.trans (neg_nonpos.mpr (sq_nonneg s)))
    change phi x ≤ _ at hh
    linarith
  have hneg : -s^2/2 < phi x0 := by rw [hphiz]; nlinarith [sq_pos_of_pos hs]
  obtain ⟨eps0,heps0,heps⟩ := Metric.isOpen_iff.mp
    (isOpen_lt continuous_const hphi.continuous) x0 hneg
  let eps := min s eps0
  have hepspos : 0 < eps := lt_min hs heps0
  refine ⟨eps,hepspos,?_,?_⟩
  · exact (min_le_left _ _).trans (by linarith)
  · intro x hx
    have hxphi : -s^2/2 < phi x := heps (ball_subset_ball (min_le_right _ _) hx)
    have hfx : f x = 0 := hcar f hf hfc hfs (-s^2/2) hres x hxphi
    have hxclosed : x ∈ closedBall x0 s := mem_closedBall.mpr
      ((mem_ball.mp hx).le.trans (min_le_left _ _))
    have he := (heta1 x hxclosed).self_of_nhds
    simpa only [f,he,one_mul] using hfx

theorem real_one_sided_zero_propagation (gamma potential psi W : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hpot : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (hpsi : ContDiff ℝ ∞ psi) (hW : ContDiff ℝ ∞ W)
    (x0 : Yau.Jets.Coord) (R : ℝ) (hR : 0 < R)
    (hzero : psi x0 = 0) (hgrad : realCoordGradient psi x0 ≠ 0) (hpos : (B x0).PosDef)
    (hEq : ∀ x ∈ ball x0 R, realEllipticResidual gamma potential B W x = 0)
    (hside : ∀ x ∈ ball x0 R, 0 ≤ psi x → W x = 0) :
    ∃ eps > 0, eps ≤ R ∧ ∀ x ∈ ball x0 eps, W x = 0 :=
  real_one_sided_strict_zero_propagation gamma potential psi W B hg hgp hpot hB hsym hpsi hW
    x0 R hR hzero hgrad hpos hEq (fun x hx hp ↦ hside x hx hp.le)

end
end Yau.Geometry

end OAI
