import OAI.Geometry.SurfaceImmersion.Atlas.QuadraticJetCutoff

namespace OAI

/-! Exact spherical second-jet cancellation by a supported quadratic map. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

def sphericalSecondFormCLM (F : Plane → Space) (p : Plane) :
    Plane →L[ℝ] Plane →L[ℝ] Space :=
  (ContinuousLinearMap.compL ℝ Plane Space Space (normalSpace F p).starProjection).comp
      (fderiv ℝ (fderiv ℝ F) p) +
    ((ContinuousLinearMap.smulRightL ℝ Plane Space).flip (F p)).comp
      (((innerSL ℝ).restrictScalars ℝ).bilinearComp (fderiv ℝ F p) (fderiv ℝ F p))

lemma sphericalSecondFormCLM_apply (F : Plane → Space) (p v w : Plane) :
    sphericalSecondFormCLM F p v w = sphericalSecondForm F p v w := rfl

lemma sphericalSecondForm_symmetric {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (p v w : Plane) : sphericalSecondForm F p v w = sphericalSecondForm F p w v := by
  unfold sphericalSecondForm secondForm
  rw [hF.contDiffAt.isSymmSndFDerivAt (by simp) v w,real_inner_comm]

lemma sphericalSecondForm_mem {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ x, ‖F x‖ = 1) (p v w : Plane) :
    sphericalSecondForm F p v w ∈ normalSpace F p := by
  apply Submodule.add_mem
  · exact Submodule.starProjection_apply_mem _ _
  · apply Submodule.smul_mem
    simpa using (normalSpace F p).neg_mem (inward_normal_mem hF hunit p)

lemma secondDerivative_add {F Q : Plane → Space}
    (hF : ContDiff ℝ ∞ F) (hQ : ContDiff ℝ ∞ Q) (p v w : Plane) :
    fderiv ℝ (fderiv ℝ (F+Q)) p v w =
      fderiv ℝ (fderiv ℝ F) p v w + fderiv ℝ (fderiv ℝ Q) p v w := by
  have he : fderiv ℝ (F+Q) = fderiv ℝ F + fderiv ℝ Q := by
    funext x
    exact fderiv_add (hF.differentiable (by simp) x) (hQ.differentiable (by simp) x)
  rw [he, fderiv_add
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p)
    ((hQ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p)]
  rfl

/-- The cutoff correction kills the spherical second fundamental form at its
center, while preserving the value and the full first derivative. -/
theorem spherical_point_flattening {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ x, ‖F x‖ = 1) (p : Plane) (χ : ContDiffBump p) :
    let Q := cutoffQuadratic (sphericalSecondFormCLM F p) p χ
    let G := radialNormalize ∘ (F+Q)
    G p = F p ∧ fderiv ℝ G p = fderiv ℝ F p ∧
      ∀ v w, sphericalSecondForm G p v w = 0 := by
  dsimp only
  let B := sphericalSecondFormCLM F p
  let Q := cutoffQuadratic B p χ
  let H := F+Q
  let G := radialNormalize ∘ H
  have hB : ∀ v w, B v w = B w v := by
    intro v w
    change sphericalSecondForm F p v w = sphericalSecondForm F p w v
    exact sphericalSecondForm_symmetric hF p v w
  have hQ := cutoffQuadratic_smooth B p χ
  obtain ⟨hq0,hq1,hq2⟩ := cutoffQuadratic_jets B hB p χ
  change Q p = 0 at hq0
  change fderiv ℝ Q p = 0 at hq1
  change ∀ v w, fderiv ℝ (fderiv ℝ Q) p v w = -B v w at hq2
  have hH : ContDiff ℝ ∞ H := hF.add hQ
  have hH0 : H p = F p := by change F p + Q p = F p; rw [hq0,add_zero]
  have hH1 : fderiv ℝ H p = fderiv ℝ F p := by
    rw [show H = F+Q from rfl, fderiv_add (hF.differentiable (by simp) p)
      (hQ.differentiable (by simp) p), hq1, add_zero]
  have hn : F p ≠ 0 := by intro hz; simpa [hz] using hunit p
  have hG0 : G p = F p := by simp [G,Function.comp_apply,hH0,radialNormalize,hunit]
  have hG1 : fderiv ℝ G p = fderiv ℝ F p := by
    ext v
    rw [show G = radialNormalize ∘ H from rfl,
      fderiv_comp p ((radialNormalize_smoothAt (by rw [hH0]; exact hn)).differentiableAt
        (by simp)) (hH.differentiable (by simp) p)]
    simp only [ContinuousLinearMap.comp_apply,hH0,hH1,
      radialNormalize_fderiv_unit (hunit p),radial_first hF hunit,zero_smul,sub_zero]
  have hN : normalSpace G p = normalSpace F p := by unfold normalSpace; rw [hG1]
  have hrad : radialNormalize ∘ F = F := by
    funext x
    simp [radialNormalize,Function.comp_apply,hunit]
  have hG2 (v w : Plane) : fderiv ℝ (fderiv ℝ G) p v w =
      fderiv ℝ (fderiv ℝ F) p v w - sphericalSecondForm F p v w := by
    have hd := radialNormalize_second_jet_difference hF hH p v w (hunit p) hH0 hH1
    rw [hrad,secondDerivative_add hF hQ,hq2] at hd
    change _ - _ = _ - inner ℝ (F p) _ • F p at hd
    have ho : inner ℝ (F p) (sphericalSecondForm F p v w) = 0 := by
      rw [real_inner_comm]
      exact sphericalSecondForm_radial_orthogonal hF hunit p v w
    change fderiv ℝ (fderiv ℝ G) p v w - _ = _ at hd
    change _ = (_ + -sphericalSecondForm F p v w - _) -
      inner ℝ (F p) (_ + -sphericalSecondForm F p v w - _) • F p at hd
    have hc : fderiv ℝ (fderiv ℝ F) p v w + -sphericalSecondForm F p v w -
        fderiv ℝ (fderiv ℝ F) p v w = -sphericalSecondForm F p v w := by abel
    rw [hc,inner_neg_right,ho,neg_zero,zero_smul,sub_zero] at hd
    exact sub_eq_iff_eq_add.mp hd |>.trans (by abel)
  refine ⟨hG0,hG1,?_⟩
  intro v w
  change sphericalSecondForm G p v w = 0
  change (normalSpace G p).starProjection (fderiv ℝ (fderiv ℝ G) p v w) +
    inner ℝ (fderiv ℝ G p v) (fderiv ℝ G p w) • G p = 0
  simp only [hN,hG2,map_sub,hG1,hG0]
  rw [Submodule.starProjection_eq_self_iff.mpr (sphericalSecondForm_mem hF hunit p v w)]
  change secondForm F p v w - sphericalSecondForm F p v w + _ = 0
  unfold sphericalSecondForm
  abel

end ClosedSurfaceR4.SphericalJets

end

end OAI
