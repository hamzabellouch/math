import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianCoefficientBounds

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E]
variable (K : E →L[ℝ] E)

def cutoffLogPotential (R s : ℝ) (z : E) : ℝ :=
  scaledCutoff R z * hermitianLogPotential K s z

def cutoffSqrtPotential (R s : ℝ) (z : E) : ℝ :=
  scaledCutoff R z * hermitianSqrtPotential K s z

lemma cutoffLogPotential_smooth (R : ℝ) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (cutoffLogPotential K R s : E → ℝ) :=
  (scaledCutoff_smooth R).mul (hermitianLogPotential_smooth K hs)

lemma cutoffSqrtPotential_smooth (R : ℝ) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (cutoffSqrtPotential K R s : E → ℝ) :=
  (scaledCutoff_smooth R).mul (hermitianSqrtPotential_smooth K hs)

lemma cutoffLogPotential_tsupport {R : ℝ} (hR : 0 < R) (s : ℝ) :
    tsupport (cutoffLogPotential K R s : E → ℝ) ⊆ closedBall 0 (2*R) :=
  tsupport_mul_subset_left.trans (scaledCutoff_tsupport hR)

lemma cutoffSqrtPotential_tsupport {R : ℝ} (hR : 0 < R) (s : ℝ) :
    tsupport (cutoffSqrtPotential K R s : E → ℝ) ⊆ closedBall 0 (2*R) :=
  tsupport_mul_subset_left.trans (scaledCutoff_tsupport hR)

lemma firstOrderSource_cutoffLog (V : E → E) (R : ℝ) {s : ℝ}
    (hs : 0 < s) (z : E) :
    firstOrderSource V (cutoffLogPotential K R s) z =
      scaledCutoff R z * hermitianLogGradientProfile K s z (V z) +
      hermitianLogPotential K s z * fderiv ℝ (scaledCutoff R) z (V z) := by
  change fderiv ℝ (fun x => scaledCutoff R x * hermitianLogPotential K s x) z (V z) = _
  rw [fderiv_fun_mul ((scaledCutoff_smooth R).differentiable (by simp) z)
      ((hermitianLogPotential_smooth K hs).differentiable (by simp) z)]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  rw [← hermitianLogGradient_eq_fderiv K hs]

lemma firstOrderSource_cutoffSqrt (V : E → E) (R : ℝ) {s : ℝ}
    (hs : 0 < s) (z : E) :
    firstOrderSource V (cutoffSqrtPotential K R s) z =
      scaledCutoff R z * hermitianSqrtGradientProfile K s z (V z) +
      hermitianSqrtPotential K s z * fderiv ℝ (scaledCutoff R) z (V z) := by
  change fderiv ℝ (fun x => scaledCutoff R x * hermitianSqrtPotential K s x) z (V z) = _
  rw [fderiv_fun_mul ((scaledCutoff_smooth R).differentiable (by simp) z)
      ((hermitianSqrtPotential_smooth K hs).differentiable (by simp) z)]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  rw [← hermitianSqrtGradient_eq_fderiv K hs]

lemma firstOrderSource_cutoffLog_compact [ProperSpace E] (V : E → E)
    {R : ℝ} (hR : 0 < R) (s : ℝ) :
    HasCompactSupport (firstOrderSource V (cutoffLogPotential K R s)) :=
  (isCompact_closedBall (0:E) (2*R)).of_isClosed_subset (isClosed_tsupport _)
    ((firstOrderSource_tsupport _ _).trans (cutoffLogPotential_tsupport K hR s))

lemma firstOrderSource_cutoffSqrt_compact [ProperSpace E] (V : E → E)
    {R : ℝ} (hR : 0 < R) (s : ℝ) :
    HasCompactSupport (firstOrderSource V (cutoffSqrtPotential K R s)) :=
  (isCompact_closedBall (0:E) (2*R)).of_isClosed_subset (isClosed_tsupport _)
    ((firstOrderSource_tsupport _ _).trans (cutoffSqrtPotential_tsupport K hR s))

end TamingCompatibility.HermitianRadial

end

end OAI
