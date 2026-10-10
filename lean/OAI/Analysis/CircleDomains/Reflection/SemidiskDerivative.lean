import OAI.Analysis.CircleDomains.Reflection.SemidiskBoundaryEstimate
import OAI.Analysis.CircleDomains.Sobolev.HalfPlaneDerivativeBound
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! The boundary barrier and Schwarz estimate give a uniform derivative
bound on a smaller half disk, hence a genuine Lipschitz extension route. -/
open Set Function Metric Filter Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma semidisk_derivative_bound {R M : ℝ} {f : ℂ → ℂ}
    (hR : 0<R) (hM : 0≤M) (hd : DifferentiableOn ℂ f (upperSemidisk R))
    (hpos : ∀z∈upperSemidisk R,0<(f z).im)
    (hbound : ∀z∈upperSemidisk R,(f z).im≤M)
    (hzero : ∀p:ℂ,‖p‖≤R → p.im=0 →
      Tendsto (fun z => (f z).im) (𝓝[upperSemidisk R] p) (𝓝 0))
    {z : ℂ} (hz : z∈upperSemidisk (R/4)) : ‖deriv f z‖≤32*M/R := by
  have hzn : ‖z‖<R/4 := mem_ball_zero_iff.mp hz.1
  have hzi : 0<z.im := hz.2
  have hzR : z∈upperSemidisk R := ⟨mem_ball_zero_iff.mpr (by linarith),hzi⟩
  have hsub : ball z (z.im/2) ⊆ upperSemidisk R := by
    intro w hw
    have hdw : ‖w-z‖<z.im/2 := by simpa only [mem_ball,dist_eq_norm] using hw
    have hn := norm_add_le (w-z) z
    rw [sub_add_cancel] at hn
    have hi := abs_im_le_norm (w-z)
    rw [sub_im] at hi
    have hil := im_le_norm z
    refine ⟨mem_ball_zero_iff.mpr (by linarith),?_⟩
    have hlow := neg_abs_le (w.im-z.im)
    change 0<w.im
    linarith
  have hs := norm_deriv_le_of_mapsTo_upper (half_pos hzi) (hd.mono hsub)
    (fun w hw => hpos w (hsub hw))
  have hb := imaginary_part_linear_boundary_bound hR hM hd hbound hzero hzR (by linarith)
  have hn : 2*(f z).im≤(32*M/R)*(z.im/2) := by
    calc
      _ ≤ 2*(8*M/R*z.im) := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = _ := by ring
  exact hs.trans ((div_le_iff₀ (half_pos hzi)).mpr hn)

lemma semidisk_lipschitz {R M : ℝ} {f : ℂ → ℂ}
    (hR : 0<R) (hM : 0≤M) (hd : DifferentiableOn ℂ f (upperSemidisk R))
    (hpos : ∀z∈upperSemidisk R,0<(f z).im)
    (hbound : ∀z∈upperSemidisk R,(f z).im≤M)
    (hzero : ∀p:ℂ,‖p‖≤R → p.im=0 →
      Tendsto (fun z => (f z).im) (𝓝[upperSemidisk R] p) (𝓝 0)) :
    ∃K:NNReal,LipschitzOnWith K f (upperSemidisk (R/4)) := by
  let K : NNReal := ⟨32*M/R,div_nonneg (mul_nonneg (by norm_num) hM) hR.le⟩
  refine ⟨K,Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℂ) ?_ ?_
    (upperSemidisk_convex (R/4))⟩
  · intro z hz
    have hzn : ‖z‖<R/4 := mem_ball_zero_iff.mp hz.1
    exact (hd z ⟨mem_ball_zero_iff.mpr (by linarith),hz.2⟩).differentiableAt
      ((upperSemidisk_open R).mem_nhds ⟨mem_ball_zero_iff.mpr (by linarith),hz.2⟩)
  · intro z hz
    change ‖fderiv ℂ f z‖≤32*M/R
    rw [←norm_deriv_eq_norm_fderiv]
    exact semidisk_derivative_bound hR hM hd hpos hbound hzero hz

end CircleDomainRigidity

end

end OAI
