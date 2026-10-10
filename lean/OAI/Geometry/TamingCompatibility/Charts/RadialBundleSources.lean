import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialShiftedSources

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

omit [InnerProductSpace ℝ E] [HasContDiffBump E] [ProperSpace E] in
lemma tsupport_translated_mul_subset {a : E → ℝ} (f : E → ℝ) (b : E) (R : ℝ)
    (ha : tsupport a ⊆ closedBall 0 R) :
    tsupport (fun z => a (z-b) * f z) ⊆ closedBall b R := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  have hn : a (z-b) ≠ 0 := fun h => hz (by simp [h])
  have hb := ha (subset_tsupport a hn)
  simpa only [mem_closedBall,dist_zero_right,dist_eq_norm,sub_zero] using hb

omit [ProperSpace E] in
lemma shiftedLogShell_support (a : E → ℝ) (V : E → E)
    {r : ℝ} (hr : 0 < r) (s : ℝ) (b : E) :
    tsupport (shiftedLogShell a V r s b) ⊆ closedBall b (4*r) :=
  tsupport_translated_mul_subset _ b _ (fun _ hz => (shellCutoff_tsupport hr hz).1)
omit [ProperSpace E] in
lemma shiftedSqrtShell_support (a : E → ℝ) (V : E → E)
    {r : ℝ} (hr : 0 < r) (s : ℝ) (b : E) :
    tsupport (shiftedSqrtShell a V r s b) ⊆ closedBall b (4*r) :=
  tsupport_translated_mul_subset _ b _ (fun _ hz => (shellCutoff_tsupport hr hz).1)
omit [ProperSpace E] in
lemma shiftedLogInner_support (a : E → ℝ) (V : E → E)
    {s : ℝ} (hs : 0 < s) (b : E) :
    tsupport (shiftedLogInner a V s b) ⊆ closedBall b (2*s) :=
  tsupport_translated_mul_subset _ b _ (scaledCutoff_tsupport hs)
omit [ProperSpace E] in
lemma shiftedSqrtInner_support (a : E → ℝ) (V : E → E)
    {s : ℝ} (hs : 0 < s) (b : E) :
    tsupport (shiftedSqrtInner a V s b) ⊆ closedBall b (2*s) :=
  tsupport_translated_mul_subset _ b _ (scaledCutoff_tsupport hs)

omit [HasContDiffBump E] [ProperSpace E] in
lemma shiftedLogSource_support (a : E → ℝ) (V : E → E) (s : ℝ) (b : E)
    (R : ℝ) (ha : tsupport a ⊆ closedBall 0 R) :
    tsupport (shiftedLogSource a V s b) ⊆ closedBall b R :=
  tsupport_translated_mul_subset _ b R ha
omit [HasContDiffBump E] [ProperSpace E] in
lemma shiftedSqrtSource_support (a : E → ℝ) (V : E → E) (s : ℝ) (b : E)
    (R : ℝ) (ha : tsupport a ⊆ closedBall 0 R) :
    tsupport (shiftedSqrtSource a V s b) ⊆ closedBall b R :=
  tsupport_translated_mul_subset _ b R ha

variable (a : E → ℝ) (V : E → E) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)

def logShellSchwartz {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedLogShell a V r s b) :=
    (isCompact_closedBall b (4*r)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedLogShell_support a V hr s b)
  exact hc.toSchwartzMap (shiftedLogShell_smooth a V ha hV r hs b)
def sqrtShellSchwartz {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedSqrtShell a V r s b) :=
    (isCompact_closedBall b (4*r)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedSqrtShell_support a V hr s b)
  exact hc.toSchwartzMap (shiftedSqrtShell_smooth a V ha hV r hs b)
def logInnerSchwartz {s : ℝ} (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedLogInner a V s b) :=
    (isCompact_closedBall b (2*s)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedLogInner_support a V hs b)
  exact hc.toSchwartzMap (shiftedLogInner_smooth a V ha hV hs b)
def sqrtInnerSchwartz {s : ℝ} (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedSqrtInner a V s b) :=
    (isCompact_closedBall b (2*s)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedSqrtInner_support a V hs b)
  exact hc.toSchwartzMap (shiftedSqrtInner_smooth a V ha hV hs b)

lemma logShellSchwartz_compact {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) :
    HasCompactSupport (logShellSchwartz a V ha hV hr hs b : E → ℝ) :=
  (isCompact_closedBall b (4*r)).of_isClosed_subset (isClosed_tsupport _)
    (shiftedLogShell_support a V hr s b)
lemma sqrtShellSchwartz_compact {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) :
    HasCompactSupport (sqrtShellSchwartz a V ha hV hr hs b : E → ℝ) :=
  (isCompact_closedBall b (4*r)).of_isClosed_subset (isClosed_tsupport _)
    (shiftedSqrtShell_support a V hr s b)
lemma logInnerSchwartz_compact {s : ℝ} (hs : 0 < s) (b : E) :
    HasCompactSupport (logInnerSchwartz a V ha hV hs b : E → ℝ) :=
  (isCompact_closedBall b (2*s)).of_isClosed_subset (isClosed_tsupport _)
    (shiftedLogInner_support a V hs b)
lemma sqrtInnerSchwartz_compact {s : ℝ} (hs : 0 < s) (b : E) :
    HasCompactSupport (sqrtInnerSchwartz a V ha hV hs b : E → ℝ) :=
  (isCompact_closedBall b (2*s)).of_isClosed_subset (isClosed_tsupport _)
    (shiftedSqrtInner_support a V hs b)

lemma logShellSchwartz_fixedSupport {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E)
    (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) :
    tsupport (logShellSchwartz a V ha hV hr hs b) ⊆ closedBall b R :=
  tsupport_mul_subset_right.trans (shiftedLogSource_support a V s b R haR)

lemma logInnerSchwartz_fixedSupport {s : ℝ} (hs : 0 < s) (b : E)
    (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) :
    tsupport (logInnerSchwartz a V ha hV hs b) ⊆ closedBall b R :=
  tsupport_mul_subset_right.trans (shiftedLogSource_support a V s b R haR)

lemma sqrtShellSchwartz_fixedSupport {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E)
    (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) :
    tsupport (sqrtShellSchwartz a V ha hV hr hs b) ⊆ closedBall b R :=
  tsupport_mul_subset_right.trans (shiftedSqrtSource_support a V s b R haR)

lemma sqrtInnerSchwartz_fixedSupport {s : ℝ} (hs : 0 < s) (b : E)
    (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) :
    tsupport (sqrtInnerSchwartz a V ha hV hs b) ⊆ closedBall b R :=
  tsupport_mul_subset_right.trans (shiftedSqrtSource_support a V s b R haR)

end TamingCompatibility.RadialPotential

end

end OAI
