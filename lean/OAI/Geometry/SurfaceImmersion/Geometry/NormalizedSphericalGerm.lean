import OAI.Geometry.SurfaceImmersion.Geometry.SphericalJetGerms

namespace OAI

/-! The local normalization calculation in a chart representative. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

theorem normalized_spherical_flattening {F Q : Plane → Space}
    (hF : ContDiff ℝ ∞ F) (hQ : ContDiff ℝ ∞ Q) {p : Plane}
    (hunit : ∀ᶠ x in 𝓝 p, ‖F x‖ = 1)
    (hq0 : Q p = 0) (hq1 : fderiv ℝ Q p = 0)
    (hq2 : ∀ v w, fderiv ℝ (fderiv ℝ Q) p v w = -sphericalSecondForm F p v w) :
    let G := radialNormalize ∘ (F+Q)
    G p = F p ∧ fderiv ℝ G p = fderiv ℝ F p ∧
      ∀ v w, sphericalSecondForm G p v w = 0 := by
  let H := F+Q
  let G := radialNormalize ∘ H
  have hp : ‖F p‖ = 1 := Filter.EventuallyEq.eq_of_nhds hunit
  have hH : ContDiff ℝ ∞ H := hF.add hQ
  have hH0 : H p = F p := by change F p + Q p = F p; rw [hq0,add_zero]
  have hH1 : fderiv ℝ H p = fderiv ℝ F p := by
    rw [show H = F+Q from rfl, fderiv_add (hF.differentiable (by simp) p)
      (hQ.differentiable (by simp) p),hq1,add_zero]
  have hn : F p ≠ 0 := by intro hz; simp [hz] at hp
  have hG0 : G p = F p := by simp [G,Function.comp_apply,hH0,radialNormalize,hp]
  have hG1 : fderiv ℝ G p = fderiv ℝ F p := by
    apply ContinuousLinearMap.ext
    intro v
    rw [show G = radialNormalize ∘ H from rfl,
      fderiv_comp p ((radialNormalize_smoothAt (by rw [hH0]; exact hn)).differentiableAt
        (by simp)) (hH.differentiable (by simp) p)]
    simp only [ContinuousLinearMap.comp_apply,hH0,hH1,
      radialNormalize_fderiv_unit hp,radial_first_of_germ hF hunit,zero_smul,sub_zero]
  have hN : normalSpace G p = normalSpace F p := by unfold normalSpace; rw [hG1]
  have hrad : radialNormalize ∘ F =ᶠ[𝓝 p] F := by
    filter_upwards [hunit] with x hx
    simp [radialNormalize,Function.comp_apply,hx]
  have hG2 (v w : Plane) : fderiv ℝ (fderiv ℝ G) p v w =
      fderiv ℝ (fderiv ℝ F) p v w - sphericalSecondForm F p v w := by
    have hd := radialNormalize_second_jet_difference hF hH p v w hp hH0 hH1
    rw [hrad.fderiv.fderiv_eq,secondDerivative_add hF hQ,hq2] at hd
    have hc : fderiv ℝ (fderiv ℝ F) p v w + -sphericalSecondForm F p v w -
        fderiv ℝ (fderiv ℝ F) p v w = -sphericalSecondForm F p v w := by abel
    have ho : inner ℝ (F p) (sphericalSecondForm F p v w) = 0 := by
      rw [real_inner_comm]
      exact sphericalSecondForm_radial_orthogonal_of_germ hF hunit v w
    rw [hc,inner_neg_right,ho,neg_zero,zero_smul,sub_zero] at hd
    exact sub_eq_iff_eq_add.mp hd |>.trans (by abel)
  refine ⟨hG0,hG1,?_⟩
  intro v w
  change (normalSpace G p).starProjection (fderiv ℝ (fderiv ℝ G) p v w) +
    inner ℝ (fderiv ℝ G p v) (fderiv ℝ G p w) • G p = 0
  simp only [hN,hG2,map_sub,hG1,hG0]
  rw [Submodule.starProjection_eq_self_iff.mpr (sphericalSecondForm_mem_of_germ hF hunit v w)]
  change secondForm F p v w - sphericalSecondForm F p v w + _ = 0
  unfold sphericalSecondForm
  abel

end ClosedSurfaceR4.SphericalJets

end

end OAI
