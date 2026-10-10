import OAI.Geometry.SurfaceImmersion.Correction.NormalizedJetCorrection
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace OAI

/-! A globally smooth extension of radial normalization that agrees with it
outside the half-unit ball. Only this fixed extension is used in atlas bounds. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

def normalizationCutoff : ContDiffBump (0 : Space) where
  rIn := 1/4
  rOut := 1/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def safeRadialNormalize (x : Space) : Space :=
  (1-normalizationCutoff x) • radialNormalize x

lemma safeRadialNormalize_eq {x : Space} (hx : (1/2 : ℝ) ≤ ‖x‖) :
    safeRadialNormalize x = radialNormalize x := by
  have hz : normalizationCutoff x = 0 := normalizationCutoff.zero_of_le_dist
    (by simpa only [normalizationCutoff,dist_zero_right] using hx)
  simp [safeRadialNormalize,hz]

lemma safeRadialNormalize_smooth : ContDiff ℝ ∞ safeRadialNormalize := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : ContDiffAt ℝ ∞ (fun _ : Space => (0 : Space)) 0 := contDiffAt_const
    apply hz.congr_of_eventuallyEq
    have he : normalizationCutoff =ᶠ[𝓝 (0 : Space)] (fun _ => (1 : ℝ)) :=
      normalizationCutoff.eventuallyEq_one
    filter_upwards [he] with y hy
    simp [safeRadialNormalize,hy]
  · exact (contDiffAt_const.sub normalizationCutoff.contDiff.contDiffAt).smul
      (radialNormalize_smoothAt hx)

end ClosedSurfaceR4.SphericalJets

end

end OAI
