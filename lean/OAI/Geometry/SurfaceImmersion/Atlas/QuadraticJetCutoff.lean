import OAI.Geometry.SurfaceImmersion.Correction.NormalizedJetCorrection

namespace OAI

/-! The local quadratic correction in the finite-point spherical preparation.
The cutoff leaves its prescribed second jet unchanged. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

def quadraticCorrection (B : Plane →L[ℝ] Plane →L[ℝ] Space) (p x : Plane) : Space :=
  (- (1 / 2 : ℝ)) • B (x-p) (x-p)

lemma quadraticCorrection_smooth (B : Plane →L[ℝ] Plane →L[ℝ] Space) (p : Plane) :
    ContDiff ℝ ∞ (quadraticCorrection B p) := by
  unfold quadraticCorrection
  exact ((B.contDiff.comp (contDiff_id.sub contDiff_const)).clm_apply
    (contDiff_id.sub contDiff_const)).const_smul _

lemma quadraticCorrection_fderiv (B : Plane →L[ℝ] Plane →L[ℝ] Space)
    (hB : ∀ v w, B v w = B w v) (p x : Plane) :
    fderiv ℝ (quadraticCorrection B p) x = - B (x-p) := by
  have hd := (B.hasFDerivAt_of_bilinear ((hasFDerivAt_id x).sub_const p)
    ((hasFDerivAt_id x).sub_const p)).const_smul (- (1 / 2 : ℝ))
  change HasFDerivAt (quadraticCorrection B p) _ x at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  change (- (1/2 : ℝ)) • (B (x-p) v + B v (x-p)) = -(B (x-p) v)
  rw [hB v (x-p)]
  module

lemma quadraticCorrection_second (B : Plane →L[ℝ] Plane →L[ℝ] Space)
    (hB : ∀ v w, B v w = B w v) (p x v w : Plane) :
    fderiv ℝ (fderiv ℝ (quadraticCorrection B p)) x v w = - B v w := by
  have he : fderiv ℝ (quadraticCorrection B p) = fun x => -B (x-p) :=
    funext (quadraticCorrection_fderiv B hB p)
  rw [he]
  have hd := (B.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p)).neg
  change HasFDerivAt (fun x => -B (x-p)) _ x at hd
  rw [hd.fderiv]
  simp

def cutoffQuadratic (B : Plane →L[ℝ] Plane →L[ℝ] Space) (p : Plane)
    (χ : ContDiffBump p) (x : Plane) : Space := χ x • quadraticCorrection B p x

lemma cutoffQuadratic_smooth (B : Plane →L[ℝ] Plane →L[ℝ] Space) (p : Plane)
    (χ : ContDiffBump p) : ContDiff ℝ ∞ (cutoffQuadratic B p χ) :=
  χ.contDiff.smul (quadraticCorrection_smooth B p)

lemma cutoffQuadratic_germ (B : Plane →L[ℝ] Plane →L[ℝ] Space) (p : Plane)
    (χ : ContDiffBump p) : cutoffQuadratic B p χ =ᶠ[𝓝 p] quadraticCorrection B p := by
  filter_upwards [χ.eventuallyEq_one] with x hx
  simp [cutoffQuadratic, hx]

lemma cutoffQuadratic_jets (B : Plane →L[ℝ] Plane →L[ℝ] Space)
    (hB : ∀ v w, B v w = B w v) (p : Plane) (χ : ContDiffBump p) :
    cutoffQuadratic B p χ p = 0 ∧ fderiv ℝ (cutoffQuadratic B p χ) p = 0 ∧
      ∀ v w, fderiv ℝ (fderiv ℝ (cutoffQuadratic B p χ)) p v w = -B v w := by
  have he := cutoffQuadratic_germ B p χ
  refine ⟨?_, ?_, ?_⟩
  · simp [cutoffQuadratic,quadraticCorrection]
  · rw [he.fderiv_eq,quadraticCorrection_fderiv B hB]
    simp
  · intro v w
    rw [he.fderiv.fderiv_eq,quadraticCorrection_second B hB]

lemma cutoffQuadratic_tsupport (B : Plane →L[ℝ] Plane →L[ℝ] Space)
    (p : Plane) (χ : ContDiffBump p) :
    tsupport (cutoffQuadratic B p χ) ⊆ closedBall p χ.rOut := by
  rw [← χ.tsupport_eq]
  change tsupport (fun x => χ x • quadraticCorrection B p x) ⊆ tsupport χ
  exact tsupport_smul_subset_left χ (quadraticCorrection B p)

lemma cutoffQuadratic_compact (B : Plane →L[ℝ] Plane →L[ℝ] Space)
    (p : Plane) (χ : ContDiffBump p) : HasCompactSupport (cutoffQuadratic B p χ) :=
  χ.hasCompactSupport.smul_right

end ClosedSurfaceR4.SphericalJets

end

end OAI
