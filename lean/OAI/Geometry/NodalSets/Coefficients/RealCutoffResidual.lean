import OAI.Geometry.NodalSets.Elliptic.RealEllipticLocalityLemmas
import OAI.Geometry.NodalSets.Elliptic.RealEllipticProducts

namespace OAI

namespace Yau.Geometry
open Filter Metric
open scoped Topology ContDiff
noncomputable section

lemma realEllipticResidual_cutoff (gamma potential eta W : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (heta : ContDiff ℝ ∞ eta) (hW : ContDiff ℝ ∞ W) (x : Yau.Jets.Coord)
    (hEq : realEllipticResidual gamma potential B W x = 0) :
    realEllipticResidual gamma potential B (fun y ↦ eta y*W y) x =
      W x*realWeightedElliptic gamma B eta x+2*realMatrixEnergy B eta W x := by
  unfold realEllipticResidual at *
  rw [real_weighted_elliptic_product gamma B eta W hg hgn hB hs heta hW]
  linear_combination eta x*hEq

lemma real_cutoff_residual_location (gamma potential eta W psi : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hpsi : Continuous psi) (x0 : Yau.Jets.Coord) (R s : ℝ)
    (heta : tsupport eta ⊆ ball x0 R)
    (heta1 : ∀ x ∈ closedBall x0 s, eta =ᶠ[𝓝 x] (fun _ ↦ 1))
    (hEq : ∀ x ∈ ball x0 R, realEllipticResidual gamma potential B W x = 0)
    (hzero : ∀ x ∈ ball x0 R, 0 < psi x → W x = 0) :
    ∀ x, realEllipticResidual gamma potential B (fun y ↦ eta y*W y) x ≠ 0 →
      x ∈ ball x0 R ∧ s ≤ dist x x0 ∧ psi x ≤ 0 := by
  intro x hx
  have hxs : x ∈ tsupport eta := tsupport_mul_subset_left
    (realEllipticResidual_tsupport gamma potential B (fun y ↦ eta y*W y) (subset_tsupport _ hx))
  have hxR := heta hxs
  refine ⟨hxR,?_,?_⟩
  · by_contra hn
    have hd : x ∈ closedBall x0 s := mem_closedBall.mpr (not_le.mp hn).le
    have he : (fun y ↦ eta y*W y) =ᶠ[𝓝 x] W := by
      filter_upwards [heta1 x hd] with y hy
      simp only [hy,one_mul]
    exact hx ((realEllipticResidual_eventuallyEq gamma potential B he).self_of_nhds.trans (hEq x hxR))
  · by_contra hn
    have hp : 0 < psi x := not_le.mp hn
    have he : (fun y ↦ eta y*W y) =ᶠ[𝓝 x] (fun _ ↦ 0) := by
      filter_upwards [isOpen_ball.mem_nhds hxR,hpsi.continuousAt.eventually (lt_mem_nhds hp)] with y hy hypsi
      simp only [hzero y hy hypsi,mul_zero]
    have hh := (realEllipticResidual_eventuallyEq gamma potential B he).self_of_nhds
    rw [realEllipticResidual_zero] at hh
    exact hx hh

end
end Yau.Geometry

end OAI
