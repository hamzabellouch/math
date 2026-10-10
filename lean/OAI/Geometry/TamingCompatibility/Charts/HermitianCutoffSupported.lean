import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.HermitianCutoffProfiles
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianTraceTranslation
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianSupportedSources

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (W : E → E →L[ℝ] E)

def translatedCutoffLog (R s : ℝ) (b z : E) : ℝ := cutoffLogPotential (W b) R s (z-b)
def translatedCutoffSqrt (R s : ℝ) (b z : E) : ℝ := cutoffSqrtPotential (W b) R s (z-b)

omit [ProperSpace E] in
lemma translatedCutoffLog_smooth (R : ℝ) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (translatedCutoffLog W R s b) :=
  (cutoffLogPotential_smooth (W b) R hs).comp (contDiff_id.sub contDiff_const)
omit [ProperSpace E] in
lemma translatedCutoffSqrt_smooth (R : ℝ) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (translatedCutoffSqrt W R s b) :=
  (cutoffSqrtPotential_smooth (W b) R hs).comp (contDiff_id.sub contDiff_const)
omit [ProperSpace E] in
lemma translatedCutoffLog_support {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    tsupport (translatedCutoffLog W R s b) ⊆ closedBall b (2*R) :=
  tsupport_translated_subset b _ (cutoffLogPotential_tsupport (W b) hR s)
omit [ProperSpace E] in
lemma translatedCutoffSqrt_support {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    tsupport (translatedCutoffSqrt W R s b) ⊆ closedBall b (2*R) :=
  tsupport_translated_subset b _ (cutoffSqrtPotential_tsupport (W b) hR s)

lemma translatedCutoffLog_compact {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    HasCompactSupport (translatedCutoffLog W R s b) :=
  (isCompact_closedBall b (2*R)).of_isClosed_subset (isClosed_tsupport _)
    (translatedCutoffLog_support W hR s b)
lemma translatedCutoffSqrt_compact {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    HasCompactSupport (translatedCutoffSqrt W R s b) :=
  (isCompact_closedBall b (2*R)).of_isClosed_subset (isClosed_tsupport _)
    (translatedCutoffSqrt_support W hR s b)

omit [ProperSpace E] in
lemma firstOrderSource_translatedCutoffLog (V : E → E) (R : ℝ) {s : ℝ}
    (hs : 0 < s) (b z : E) :
    firstOrderSource V (translatedCutoffLog W R s b) z =
      shiftedLogSource W (scaledCutoff R) V s b z + shiftedLogError W V R s b z := by
  change fderiv ℝ (fun z => cutoffLogPotential (W b) R s (z-b)) z (V z) = _
  rw [fderiv_comp_sub]
  simpa [firstOrderSource,shiftedLogSource,logSingularSource,shiftedLogError,cutoffLogError] using
    firstOrderSource_cutoffLog (W b) (fun w => V (b+w)) R hs (z-b)
omit [ProperSpace E] in
lemma firstOrderSource_translatedCutoffSqrt (V : E → E) (R : ℝ) {s : ℝ}
    (hs : 0 < s) (b z : E) :
    firstOrderSource V (translatedCutoffSqrt W R s b) z =
      shiftedSqrtSource W (scaledCutoff R) V s b z + shiftedSqrtError W V R s b z := by
  change fderiv ℝ (fun z => cutoffSqrtPotential (W b) R s (z-b)) z (V z) = _
  rw [fderiv_comp_sub]
  simpa [firstOrderSource,shiftedSqrtSource,sqrtSingularSource,shiftedSqrtError,cutoffSqrtError] using
    firstOrderSource_cutoffSqrt (W b) (fun w => V (b+w)) R hs (z-b)

variable (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) {R s : ℝ} (hR : 0 < R) (hs : 0 < s)

def logCutoffSourceSupported (K : Set E) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    supportedSchwartz K := by
  let f := firstOrderSource V (translatedCutoffLog W R s b)
  have hf : ContDiff ℝ ∞ f := firstOrderSource_smooth V hV _ (translatedCutoffLog_smooth W R hs b)
  have hc : HasCompactSupport f := (translatedCutoffLog_compact W hR s b).of_isClosed_subset
    (isClosed_tsupport _) (firstOrderSource_tsupport _ _)
  exact ⟨hc.toSchwartzMap hf, ((firstOrderSource_tsupport _ _).trans
    (translatedCutoffLog_support W hR s b)).trans hb⟩
def sqrtCutoffSourceSupported (K : Set E) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    supportedSchwartz K := by
  let f := firstOrderSource V (translatedCutoffSqrt W R s b)
  have hf : ContDiff ℝ ∞ f := firstOrderSource_smooth V hV _ (translatedCutoffSqrt_smooth W R hs b)
  have hc : HasCompactSupport f := (translatedCutoffSqrt_compact W hR s b).of_isClosed_subset
    (isClosed_tsupport _) (firstOrderSource_tsupport _ _)
  exact ⟨hc.toSchwartzMap hf, ((firstOrderSource_tsupport _ _).trans
    (translatedCutoffSqrt_support W hR s b)).trans hb⟩

lemma logCutoffSourceSupported_eq (K : Set E) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    logCutoffSourceSupported W V hV hR hs K b hb =
      logSourceSupported W (scaledCutoff R) V (scaledCutoff_smooth R) hV
        (2*R) (scaledCutoff_tsupport hR) K hs b hb + logErrorSupported W V hW hV hR K s b hb := by
  apply Subtype.ext
  ext z
  exact firstOrderSource_translatedCutoffLog W V R hs b z
lemma sqrtCutoffSourceSupported_eq (K : Set E) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    sqrtCutoffSourceSupported W V hV hR hs K b hb =
      sqrtSourceSupported W (scaledCutoff R) V (scaledCutoff_smooth R) hV
        (2*R) (scaledCutoff_tsupport hR) K hs b hb + sqrtErrorSupported W V hW hV hR K s b hb := by
  apply Subtype.ext
  ext z
  exact firstOrderSource_translatedCutoffSqrt W V R hs b z

end TamingCompatibility.HermitianRadial

end
end

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric ContinuousAlternatingMap
open scoped ContDiff Topology SchwartzMap RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E]

lemma translatedCutoffLog_germ (W : E → E →L[ℝ] E) {R : ℝ} (hR : 0 < R)
    (s : ℝ) (b : E) {y : E} (hy : ‖y-b‖ < R) :
    translatedCutoffLog W R s b =ᶠ[𝓝 y] fun x => hermitianLogPotential (W b) s (x-b) := by
  have he : ∀ᶠ x in 𝓝 y, ‖x-b‖ < R :=
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hy
  filter_upwards [he] with x hx
  exact show scaledCutoff R (x-b) * hermitianLogPotential (W b) s (x-b) = _ by
    rw [scaledCutoff_one hR hx.le,one_mul]

lemma translatedCutoffSqrt_germ (W : E → E →L[ℝ] E) {R : ℝ} (hR : 0 < R)
    (s : ℝ) (b : E) {y : E} (hy : ‖y-b‖ < R) :
    translatedCutoffSqrt W R s b =ᶠ[𝓝 y] fun x => hermitianSqrtPotential (W b) s (x-b) := by
  have he : ∀ᶠ x in 𝓝 y, ‖x-b‖ < R :=
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hy
  filter_upwards [he] with x hx
  exact show scaledCutoff R (x-b) * hermitianSqrtPotential (W b) s (x-b) = _ by
    rw [scaledCutoff_one hR hx.le,one_mul]

lemma cutoffLog_trace_lower (W : 𝓢(E,E →L[ℝ] E)) {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (b y v : E) (hy : ‖y-b‖ < R)
    (hWy : ∀ w, W y (W y w) = -w) (hWb : ∀ w, W b (W b w) = -w) :
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    2*s^2*(‖v‖^2+‖W b v‖^2)/(s^2+‖y-b‖^2+‖W b (y-b)‖^2)^2 -
      ((1+M)^2*(16*L*M/(s+‖y-b‖)))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc W (translatedCutoffLog W R s b)) y ![v,W y v] := by
  rw [ExteriorForms.extDeriv_dc_congr_germ Filter.EventuallyEq.rfl
    (translatedCutoffLog_germ W hR s b hy)]
  exact schwartz_hermitianLog_lower W hs b y v hWy hWb

lemma cutoffSqrt_trace_lower (W : 𝓢(E,E →L[ℝ] E)) {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (b y v : E) (hy : ‖y-b‖ < R)
    (hWy : ∀ w, W y (W y w) = -w) (hWb : ∀ w, W b (W b w) = -w) :
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    ‖v‖^2/((1+M)*(s+‖y-b‖)) - ((1+M)^2*(10*L*M))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc W (translatedCutoffSqrt W R s b)) y ![v,W y v] := by
  rw [ExteriorForms.extDeriv_dc_congr_germ Filter.EventuallyEq.rfl
    (translatedCutoffSqrt_germ W hR s b hy)]
  exact schwartz_hermitianSqrt_lower W hs b y v hWy hWb
end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
