import OAI.Analysis.CircleDomains.Reflection.UpperSemidisk

namespace OAI

/-! Linear decay of the imaginary part at a straight boundary. Only the
imaginary trace is prescribed; no complex boundary value is assumed. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma imaginary_part_le_semidisk_barrier {R M : ℝ} {f : ℂ → ℂ}
    (hR : 0<R) (hM : 0≤M) (hd : DifferentiableOn ℂ f (upperSemidisk R))
    (hbound : ∀z∈upperSemidisk R,(f z).im≤M)
    (hzero : ∀p:ℂ,‖p‖≤R → p.im=0 →
      Tendsto (fun z => (f z).im) (𝓝[upperSemidisk R] p) (𝓝 0)) :
    ∀z∈upperSemidisk R,(f z).im≤M*(semidiskBarrier R z).im := by
  let g : ℂ → ℂ := fun z => -I*(f z-(M : ℂ)*semidiskBarrier R z)
  have hgre (z : ℂ) : (g z).re=(f z).im-M*(semidiskBarrier R z).im := by
    simp [g]
  have hgd : DifferentiableOn ℂ g (upperSemidisk R) := by
    intro z hz
    obtain ⟨h₁,h₂⟩ := semidiskBarrier_den_ne_zero hz.2
    exact (((hd z hz).differentiableAt ((upperSemidisk_open R).mem_nhds hz)).sub
      ((differentiableAt_semidiskBarrier h₁ h₂).const_mul (M : ℂ))).const_mul (-I)
      |>.differentiableWithinAt
  have hmax := real_part_le_of_boundary_upper_limits (upperSemidisk_open R)
    (upperSemidisk_convex R).isPreconnected (upperSemidisk_compact_closure R)
    (upperSemidisk_frontier_nonempty hR) hgd (C := 0) ?_
  · intro z hz
    have h := hmax z hz
    rw [hgre] at h
    linarith
  · intro p hp ε hε
    obtain ⟨hn,hp0,hcase⟩ := upperSemidisk_frontier_cases hp
    by_cases him : p.im=0
    · have ht := (hzero p hn him).eventually (gt_mem_nhds hε)
      have hmem : ∀ᶠ z in 𝓝[upperSemidisk R] p,z∈upperSemidisk R := self_mem_nhdsWithin
      filter_upwards [ht,hmem] with z hz hzu
      rw [hgre]
      have hb := semidiskBarrier_im_nonneg hR.le hzu.2.le
      nlinarith
    · have hpos : 0<p.im := lt_of_le_of_ne hp0 (Ne.symm him)
      have hnorm : ‖p‖=R := hcase.resolve_right him
      obtain ⟨h₁,h₂⟩ := semidiskBarrier_den_ne_zero hpos
      have hc : ContinuousAt (fun z : ℂ => (semidiskBarrier R z).im) p :=
        continuous_im.continuousAt.comp (differentiableAt_semidiskBarrier h₁ h₂).continuousAt
      have ht : Tendsto (fun z : ℂ => M-M*(semidiskBarrier R z).im)
          (𝓝[upperSemidisk R] p) (𝓝 (M-M*(semidiskBarrier R p).im)) :=
        ((continuousAt_const.sub (continuousAt_const.mul hc)).tendsto).mono_left nhdsWithin_le_nhds
      have hle : M-M*(semidiskBarrier R p).im≤0 := by
        have h := semidiskBarrier_im_ge_one_on_arc hR hpos hnorm
        nlinarith
      have he := ht.eventually (gt_mem_nhds (lt_of_le_of_lt hle hε))
      have hmem : ∀ᶠ z in 𝓝[upperSemidisk R] p,z∈upperSemidisk R := self_mem_nhdsWithin
      filter_upwards [he,hmem] with z hz hzu
      rw [hgre]
      have hb := hbound z hzu
      linarith

lemma imaginary_part_linear_boundary_bound {R M : ℝ} {f : ℂ → ℂ}
    (hR : 0<R) (hM : 0≤M) (hd : DifferentiableOn ℂ f (upperSemidisk R))
    (hbound : ∀z∈upperSemidisk R,(f z).im≤M)
    (hzero : ∀p:ℂ,‖p‖≤R → p.im=0 →
      Tendsto (fun z => (f z).im) (𝓝[upperSemidisk R] p) (𝓝 0))
    {z : ℂ} (hz : z∈upperSemidisk R) (hn : ‖z‖≤R/2) :
    (f z).im≤8*M/R*z.im := by
  calc
    _ ≤ M*(semidiskBarrier R z).im := imaginary_part_le_semidisk_barrier hR hM hd hbound hzero z hz
    _ ≤ M*(8*z.im/R) := mul_le_mul_of_nonneg_left (semidiskBarrier_im_le hR hz.2.le hn) hM
    _ = _ := by ring

end CircleDomainRigidity

end

end OAI
