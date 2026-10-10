import OAI.Analysis.CircleDomains.Modulus.LocalGraphCapacity
import OAI.Analysis.CircleDomains.Selection.CountableGraphCover
import OAI.Analysis.CircleDomains.Sobolev.SobolevGraphEnergy

namespace OAI

/-! The local capacity estimate as a natural-number cover of the actual
Sobolev graph inside an ambient ball. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma sobolev_graph_local_cover {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    (E : Set EuclideanPlane) (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖deriv scalarCapacityBump y‖ ≤ C)
    (hηd : ∀ y, ‖fderiv ℝ spatialCapacityBump y‖ ≤ C) :
    ∃ T : ℕ → Set GraphSpace,
      sobolevGraph u '' E ∩ closedBall (euclideanPlaneCoordinates a,t) s ⊆ ⋃ n, T n ∧
      (∀ n, ediam (T n) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' n, ediam (T n)^2) ≤
        (4194304 * ENNReal.ofReal (1+8*C^2)) *
          sobolevGraphEnergy u W.weakGrad (closedBall (euclideanPlaneCoordinates a,t) (4*s)) := by
  let A : Set (ℝ × ℝ) := {p | a+s • euclideanPlaneCoordinates.symm p ∈ E ∧
    p ∈ closedBall 0 1 ∧ |u (a+s • euclideanPlaneCoordinates.symm p)-t| ≤ s}
  obtain ⟨U,N,T,hU,hcover,hdiam,hcost⟩ := local_graph_capacity_cover hu W hsu a t hs hC0 hC hηd
    (A := A) (fun _ hp => hp.2.1) (fun _ hp => hp.2.2)
  have : Countable U := hU.to_subtype
  let S : (Σ x : U, Fin (N x)) → Set GraphSpace := fun i => T i.1 i.2
  obtain ⟨B,hB,hBd,hBc⟩ := nat_graph_cover_of_countable S
    (fun i => hdiam i.1 i.2)
  refine ⟨B,?_,hBd,?_⟩
  · rintro z ⟨⟨y,hy,rfl⟩,hz⟩
    let p := euclideanPlaneCoordinates ((planarAffineHomeomorph a s hs.ne').symm y)
    have hp : a+s • euclideanPlaneCoordinates.symm p = y := by
      dsimp only [p]
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact (planarAffineHomeomorph a s hs.ne').apply_symm_apply y
    have hb : dist (euclideanPlaneCoordinates y) (euclideanPlaneCoordinates a) ≤ s ∧
        |u y-t| ≤ s := by
      simpa only [mem_closedBall,sobolevGraph,Prod.dist_eq,max_le_iff,Real.dist_eq] using hz
    have hunit : p ∈ closedBall 0 1 := by
      have he : euclideanPlaneCoordinates y - euclideanPlaneCoordinates a = s • p := by
        rw [← hp,map_add,map_smul,ContinuousLinearEquiv.apply_symm_apply,add_sub_cancel_left]
      have hn : s*‖p‖ ≤ s := by
        simpa only [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_pos hs] using hb.1
      have hpn : ‖p‖ ≤ 1 := by nlinarith
      simpa only [mem_closedBall,dist_zero_right] using hpn
    have hpA : p ∈ A := by
      change a+s • euclideanPlaneCoordinates.symm p ∈ E ∧ _
      exact ⟨by rwa [hp],hunit,by simpa only [hp] using hb.2⟩
    have hin := hcover (mem_image_of_mem _ hpA)
    rw [hp] at hin
    rw [← hB]
    simpa only [S,iUnion_sigma,sobolevGraph] using hin
  · rw [hBc,ENNReal.tsum_sigma']
    exact hcost.trans (mul_le_mul' le_rfl (sobolev_graph_band_energy_le_ball hu W.weakGrad a t hs.le))

end CircleDomainRigidity

end

end OAI
