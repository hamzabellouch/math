import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialGradientBridge

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E]

def cutoffLogPotential (R s : ℝ) (z : E) : ℝ :=
  scaledCutoff R z * logPotential s z

def cutoffSqrtPotential (R s : ℝ) (z : E) : ℝ :=
  scaledCutoff R z * sqrtPotential s z

lemma cutoffLogPotential_smooth (R : ℝ) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (cutoffLogPotential R s : E → ℝ) :=
  (scaledCutoff_smooth R).mul (logPotential_smooth hs)

lemma cutoffSqrtPotential_smooth (R : ℝ) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (cutoffSqrtPotential R s : E → ℝ) :=
  (scaledCutoff_smooth R).mul (sqrtPotential_smooth hs)

lemma cutoffLogPotential_tsupport {R : ℝ} (hR : 0 < R) (s : ℝ) :
    tsupport (cutoffLogPotential R s : E → ℝ) ⊆ closedBall 0 (2*R) :=
  tsupport_mul_subset_left.trans (scaledCutoff_tsupport hR)

lemma cutoffSqrtPotential_tsupport {R : ℝ} (hR : 0 < R) (s : ℝ) :
    tsupport (cutoffSqrtPotential R s : E → ℝ) ⊆ closedBall 0 (2*R) :=
  tsupport_mul_subset_left.trans (scaledCutoff_tsupport hR)

def firstOrderSource (V : E → E) (u : E → ℝ) (z : E) : ℝ :=
  fderiv ℝ u z (V z)

omit [HasContDiffBump E] in
lemma firstOrderSource_smooth (V : E → E) (hV : ContDiff ℝ ∞ V)
    (u : E → ℝ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (firstOrderSource V u) := by
  exact (hu.fderiv_right (by simp)).clm_apply hV

omit [HasContDiffBump E] in
lemma firstOrderSource_tsupport (V : E → E) (u : E → ℝ) :
    tsupport (firstOrderSource V u) ⊆ tsupport u := by
  apply (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  change fderiv ℝ u z ≠ 0
  intro h
  exact hz (by simp [firstOrderSource,h])

lemma firstOrderSource_cutoffLog (V : E → E) (R : ℝ) {s : ℝ}
    (hs : 0 < s) (z : E) :
    firstOrderSource V (cutoffLogPotential R s) z =
      scaledCutoff R z * logGradientProfile s z (V z) +
      logPotential s z * fderiv ℝ (scaledCutoff R) z (V z) := by
  change fderiv ℝ (fun x => scaledCutoff R x * logPotential s x) z (V z) = _
  rw [fderiv_fun_mul ((scaledCutoff_smooth R).differentiable (by simp) z)
      ((logPotential_smooth hs).differentiable (by simp) z)]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  rw [← logGradientProfile_eq_fderiv hs]

lemma firstOrderSource_cutoffSqrt (V : E → E) (R : ℝ) {s : ℝ}
    (hs : 0 < s) (z : E) :
    firstOrderSource V (cutoffSqrtPotential R s) z =
      scaledCutoff R z * sqrtGradientProfile s z (V z) +
      sqrtPotential s z * fderiv ℝ (scaledCutoff R) z (V z) := by
  change fderiv ℝ (fun x => scaledCutoff R x * sqrtPotential s x) z (V z) = _
  rw [fderiv_fun_mul ((scaledCutoff_smooth R).differentiable (by simp) z)
      ((sqrtPotential_smooth hs).differentiable (by simp) z)]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  rw [← sqrtGradientProfile_eq_fderiv hs]

lemma firstOrderSource_cutoffLog_compact [ProperSpace E] (V : E → E)
    {R : ℝ} (hR : 0 < R) (s : ℝ) :
    HasCompactSupport (firstOrderSource V (cutoffLogPotential R s)) :=
  (isCompact_closedBall (0:E) (2*R)).of_isClosed_subset (isClosed_tsupport _)
    ((firstOrderSource_tsupport _ _).trans (cutoffLogPotential_tsupport hR s))

lemma firstOrderSource_cutoffSqrt_compact [ProperSpace E] (V : E → E)
    {R : ℝ} (hR : 0 < R) (s : ℝ) :
    HasCompactSupport (firstOrderSource V (cutoffSqrtPotential R s)) :=
  (isCompact_closedBall (0:E) (2*R)).of_isClosed_subset (isClosed_tsupport _)
    ((firstOrderSource_tsupport _ _).trans (cutoffSqrtPotential_tsupport hR s))

end TamingCompatibility.RadialPotential

end

end OAI
