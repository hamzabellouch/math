import OAI.Geometry.SurfaceImmersion.Geometry.SphericalJets
import OAI.Geometry.Immersion.ClosedSurface.MetricModel

namespace OAI

/-! Second jets of radial normalization, for the finite-point flattening
of the starting spherical immersion. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

/-- Radial normalization is kept as an actual map of Euclidean four-space. -/
def radialNormalize (x : Space) : Space := ‖x‖⁻¹ • x

lemma radialNormalize_smoothAt {x : Space} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ radialNormalize x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

lemma radialNormalize_fderiv_unit {x : Space} (hx : ‖x‖ = 1) (v : Space) :
    fderiv ℝ radialNormalize x v = v - inner ℝ x v • x := by
  have hs := (hasFDerivAt_id x).norm_sq.sqrt (by simp [hx] : ‖x‖^2 ≠ 0)
  have hi := (hasDerivAt_inv (by simp [hx] : Real.sqrt (‖x‖^2) ≠ 0)).comp_hasFDerivAt x hs
  have hd := hi.smul (hasFDerivAt_id x)
  have he : (fun y : Space => (Real.sqrt (‖y‖^2))⁻¹ • y) = radialNormalize := by
    funext y
    simp [radialNormalize]
  change HasFDerivAt (fun y : Space => (Real.sqrt (‖y‖^2))⁻¹ • y) _ x at hd
  rw [he] at hd
  rw [hd.fderiv]
  simp [hx,ContinuousLinearMap.smulRight_apply,sub_eq_add_neg,neg_smul]

lemma secondDerivative_apply {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {f : E → H} {p : E}
    (hf : ContDiffAt ℝ ∞ f p) (v w : E) :
    fderiv ℝ (fun q => fderiv ℝ f q w) p v = fderiv ℝ (fderiv ℝ f) p v w := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    (differentiableAt_const w)]
  simp

lemma secondDerivative_comp {E H Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E → H} {g : H → Z} {U : Set H} (hf : ContDiff ℝ ∞ f)
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) {p : E} (hp : f p ∈ U) (v w : E) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) p v w =
      fderiv ℝ (fderiv ℝ g) (f p) (fderiv ℝ f p v) (fderiv ℝ f p w) +
      fderiv ℝ g (f p) (fderiv ℝ (fderiv ℝ f) p v w) := by
  have hgp := hg.contDiffAt (hU.mem_nhds hp)
  have hDg := hgp.fderiv_right (m := ∞) (by simp)
  have hD1 := (hDg.differentiableAt (by simp)).hasFDerivAt.comp p
    (hf.differentiable (by simp) p).hasFDerivAt
  have hD2 := (((hf.fderiv_right (m := ∞) (by simp)).clm_apply
    (show ContDiff ℝ ∞ (fun _ : E => w) from contDiff_const)).differentiable (by simp) p).hasFDerivAt
  have hd := hD1.clm_apply hD2
  have he : (fun q => fderiv ℝ g (f q) (fderiv ℝ f q w)) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ (g ∘ f) q w) := by
    filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)] with q hq
    rw [fderiv_comp q ((hg.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
      (hf.differentiable (by simp) q)]
    rfl
  have hev := congrArg (fun L : E →L[ℝ] Z => L v) (he.fderiv_eq.symm.trans hd.fderiv)
  rw [secondDerivative_apply (hgp.comp p hf.contDiffAt)] at hev
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    Function.comp_apply] at hev
  rw [secondDerivative_apply hf.contDiffAt] at hev
  simpa only [add_comm] using hev

/-- Maps with identical value and first derivative differ after radial
normalization by the differential of normalization applied to their
second-jet difference. -/
theorem radialNormalize_second_jet_difference {F G : Plane → Space}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (p v w : Plane)
    (hFp : ‖F p‖ = 1) (hvalue : G p = F p)
    (hfirst : fderiv ℝ G p = fderiv ℝ F p) :
    fderiv ℝ (fderiv ℝ (radialNormalize ∘ G)) p v w -
      fderiv ℝ (fderiv ℝ (radialNormalize ∘ F)) p v w =
    (fderiv ℝ (fderiv ℝ G) p v w - fderiv ℝ (fderiv ℝ F) p v w) -
      inner ℝ (F p) (fderiv ℝ (fderiv ℝ G) p v w - fderiv ℝ (fderiv ℝ F) p v w) • F p := by
  have hne : F p ≠ 0 := by intro hz; simp [hz] at hFp
  have hU : IsOpen ({x : Space | x ≠ 0}) := isOpen_ne_fun continuous_id continuous_const
  have hn : ContDiffOn ℝ ∞ radialNormalize {x : Space | x ≠ 0} :=
    fun x hx => (radialNormalize_smoothAt hx).contDiffWithinAt
  rw [secondDerivative_comp hG hU hn (by change G p ≠ 0; rw [hvalue]; exact hne),
    secondDerivative_comp hF hU hn hne,hvalue,hfirst]
  have he : ∀ a b c : Space, (a+b)-(a+c) = b-c := fun a b c => by abel
  rw [he,← map_sub,radialNormalize_fderiv_unit hFp]

end ClosedSurfaceR4.SphericalJets

end

end OAI
