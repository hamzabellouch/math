import OAI.Geometry.SurfaceImmersion.Geometry.SphericalPointFlattening

namespace OAI

/-! Local versions of the spherical identities. Chart representatives need
take values in the sphere only near the point under consideration. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

lemma radial_first_of_germ {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    {p : Plane} (hunit : ∀ᶠ x in 𝓝 p, ‖F x‖ = 1) (v : Plane) :
    inner ℝ (F p) (fderiv ℝ F p v) = 0 := by
  have he : (fun y => inner ℝ (F y) (F y)) =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
    filter_upwards [hunit] with y hy
    rw [real_inner_self_eq_norm_sq,hy]
    norm_num
  have hh := congrArg (fun A : Plane →L[ℝ] ℝ => A v) he.fderiv_eq
  rw [fderiv_inner_apply ℝ (hF.differentiable (by simp) p)
    (hF.differentiable (by simp) p)] at hh
  simp only [fderiv_const_apply,zero_apply,real_inner_comm (F p)] at hh
  linarith

lemma radial_second_of_germ {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    {p : Plane} (hunit : ∀ᶠ x in 𝓝 p, ‖F x‖ = 1) (v w : Plane) :
    inner ℝ (F p) (fderiv ℝ (fderiv ℝ F) p v w) =
      -inner ℝ (fderiv ℝ F p v) (fderiv ℝ F p w) := by
  have he : (fun y => inner ℝ (F y) (fderiv ℝ F y w)) =ᶠ[𝓝 p]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hunit.eventually_nhds] with y hy
    exact radial_first_of_germ hF hy w
  have hh := congrArg (fun A : Plane →L[ℝ] ℝ => A v) he.fderiv_eq
  have hD := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p
  rw [fderiv_inner_apply ℝ (hF.differentiable (by simp) p)
    (hD.clm_apply (differentiableAt_const w)),derivative_apply hF] at hh
  simp only [fderiv_const_apply,zero_apply] at hh
  linarith

lemma radial_normal_mem_of_germ {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    {p : Plane} (hunit : ∀ᶠ x in 𝓝 p, ‖F x‖ = 1) :
    F p ∈ normalSpace F p := by
  rw [normalSpace,Submodule.mem_orthogonal]
  rintro _ ⟨v,rfl⟩
  change inner ℝ (fderiv ℝ F p v) (F p) = 0
  rw [real_inner_comm]
  exact radial_first_of_germ hF hunit v

lemma sphericalSecondForm_mem_of_germ {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    {p : Plane} (hunit : ∀ᶠ x in 𝓝 p, ‖F x‖ = 1) (v w : Plane) :
    sphericalSecondForm F p v w ∈ normalSpace F p := by
  exact Submodule.add_mem _ (Submodule.starProjection_apply_mem _ _)
    (Submodule.smul_mem _ _ (radial_normal_mem_of_germ hF hunit))

lemma sphericalSecondForm_radial_orthogonal_of_germ {F : Plane → Space}
    (hF : ContDiff ℝ ∞ F) {p : Plane} (hunit : ∀ᶠ x in 𝓝 p, ‖F x‖ = 1)
    (v w : Plane) : inner ℝ (sphericalSecondForm F p v w) (F p) = 0 := by
  have hp : ‖F p‖ = 1 := Filter.EventuallyEq.eq_of_nhds hunit
  have hnorm : inner ℝ (F p) (F p) = 1 := by rw [real_inner_self_eq_norm_sq,hp]; norm_num
  rw [sphericalSecondForm,inner_add_left,real_inner_smul_left,hnorm,mul_one,
    secondForm,Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (radial_normal_mem_of_germ hF hunit),
    real_inner_comm,radial_second_of_germ hF hunit]
  exact neg_add_cancel _

end ClosedSurfaceR4.SphericalJets

end

end OAI
