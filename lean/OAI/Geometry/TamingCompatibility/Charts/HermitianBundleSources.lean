import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianShiftedSources

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

omit [ProperSpace E] in
lemma shiftedLogShell_support (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {r : ℝ} (hr : 0 < r) (s : ℝ) (b : E) :
    tsupport (shiftedLogShell W a V r s b) ⊆ closedBall b (4*r) :=
  tsupport_translated_mul_subset _ b _ (fun _ hz => (shellCutoff_tsupport hr hz).1)
omit [ProperSpace E] in
lemma shiftedSqrtShell_support (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {r : ℝ} (hr : 0 < r) (s : ℝ) (b : E) :
    tsupport (shiftedSqrtShell W a V r s b) ⊆ closedBall b (4*r) :=
  tsupport_translated_mul_subset _ b _ (fun _ hz => (shellCutoff_tsupport hr hz).1)
omit [ProperSpace E] in
lemma shiftedLogInner_support (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {s : ℝ} (hs : 0 < s) (b : E) :
    tsupport (shiftedLogInner W a V s b) ⊆ closedBall b (2*s) :=
  tsupport_translated_mul_subset _ b _ (scaledCutoff_tsupport hs)
omit [ProperSpace E] in
lemma shiftedSqrtInner_support (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    {s : ℝ} (hs : 0 < s) (b : E) :
    tsupport (shiftedSqrtInner W a V s b) ⊆ closedBall b (2*s) :=
  tsupport_translated_mul_subset _ b _ (scaledCutoff_tsupport hs)

omit [HasContDiffBump E] [ProperSpace E] in
lemma shiftedLogSource_support (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (s : ℝ) (b : E)
    (R : ℝ) (ha : tsupport a ⊆ closedBall 0 R) :
    tsupport (shiftedLogSource W a V s b) ⊆ closedBall b R :=
  tsupport_translated_mul_subset _ b R ha
omit [HasContDiffBump E] [ProperSpace E] in
lemma shiftedSqrtSource_support (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (s : ℝ) (b : E)
    (R : ℝ) (ha : tsupport a ⊆ closedBall 0 R) :
    tsupport (shiftedSqrtSource W a V s b) ⊆ closedBall b R :=
  tsupport_translated_mul_subset _ b R ha

variable (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)

def logShellSchwartz {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedLogShell W a V r s b) :=
    (isCompact_closedBall b (4*r)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedLogShell_support W a V hr s b)
  exact hc.toSchwartzMap (shiftedLogShell_smooth W a V ha hV r hs b)
def sqrtShellSchwartz {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedSqrtShell W a V r s b) :=
    (isCompact_closedBall b (4*r)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedSqrtShell_support W a V hr s b)
  exact hc.toSchwartzMap (shiftedSqrtShell_smooth W a V ha hV r hs b)
def logInnerSchwartz {s : ℝ} (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedLogInner W a V s b) :=
    (isCompact_closedBall b (2*s)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedLogInner_support W a V hs b)
  exact hc.toSchwartzMap (shiftedLogInner_smooth W a V ha hV hs b)
def sqrtInnerSchwartz {s : ℝ} (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedSqrtInner W a V s b) :=
    (isCompact_closedBall b (2*s)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedSqrtInner_support W a V hs b)
  exact hc.toSchwartzMap (shiftedSqrtInner_smooth W a V ha hV hs b)

lemma logShellSchwartz_compact {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) :
    HasCompactSupport (logShellSchwartz W a V ha hV hr hs b : E → ℝ) :=
  (isCompact_closedBall b (4*r)).of_isClosed_subset (isClosed_tsupport _)
    (shiftedLogShell_support W a V hr s b)
lemma sqrtShellSchwartz_compact {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) :
    HasCompactSupport (sqrtShellSchwartz W a V ha hV hr hs b : E → ℝ) :=
  (isCompact_closedBall b (4*r)).of_isClosed_subset (isClosed_tsupport _)
    (shiftedSqrtShell_support W a V hr s b)
lemma logInnerSchwartz_compact {s : ℝ} (hs : 0 < s) (b : E) :
    HasCompactSupport (logInnerSchwartz W a V ha hV hs b : E → ℝ) :=
  (isCompact_closedBall b (2*s)).of_isClosed_subset (isClosed_tsupport _)
    (shiftedLogInner_support W a V hs b)
lemma sqrtInnerSchwartz_compact {s : ℝ} (hs : 0 < s) (b : E) :
    HasCompactSupport (sqrtInnerSchwartz W a V ha hV hs b : E → ℝ) :=
  (isCompact_closedBall b (2*s)).of_isClosed_subset (isClosed_tsupport _)
    (shiftedSqrtInner_support W a V hs b)

lemma logShellSchwartz_fixedSupport {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E)
    (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) :
    tsupport (logShellSchwartz W a V ha hV hr hs b) ⊆ closedBall b R :=
  tsupport_mul_subset_right.trans (shiftedLogSource_support W a V s b R haR)

lemma logInnerSchwartz_fixedSupport {s : ℝ} (hs : 0 < s) (b : E)
    (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) :
    tsupport (logInnerSchwartz W a V ha hV hs b) ⊆ closedBall b R :=
  tsupport_mul_subset_right.trans (shiftedLogSource_support W a V s b R haR)

lemma sqrtShellSchwartz_fixedSupport {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E)
    (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) :
    tsupport (sqrtShellSchwartz W a V ha hV hr hs b) ⊆ closedBall b R :=
  tsupport_mul_subset_right.trans (shiftedSqrtSource_support W a V s b R haR)

lemma sqrtInnerSchwartz_fixedSupport {s : ℝ} (hs : 0 < s) (b : E)
    (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) :
    tsupport (sqrtInnerSchwartz W a V ha hV hs b) ⊆ closedBall b R :=
  tsupport_mul_subset_right.trans (shiftedSqrtSource_support W a V s b R haR)

end TamingCompatibility.HermitianRadial

end

end OAI
