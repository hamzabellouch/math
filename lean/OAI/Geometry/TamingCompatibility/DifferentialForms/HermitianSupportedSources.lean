import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianErrorSources

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
  (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) (K : Set E)

def logShellSupported {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨logShellSchwartz W a V ha hV hr hs b,(logShellSchwartz_fixedSupport W a V ha hV hr hs b R haR).trans hb⟩

def logInnerSupported {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨logInnerSchwartz W a V ha hV hs b,(logInnerSchwartz_fixedSupport W a V ha hV hs b R haR).trans hb⟩

def logSourceSupported {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨logSourceSchwartz W a V ha hV R haR hs b,(shiftedLogSource_support W a V s b R haR).trans hb⟩

lemma logSupported_reconstruction {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K)
    (N : ℕ) (hN : R ≤ s*2^N) :
    logSourceSupported W a V ha hV R haR K hs b hb =
      logInnerSupported W a V ha hV R haR K hs b hb +
      ∑ j ∈ Finset.range N, logShellSupported W a V ha hV R haR K
        (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b hb := by
  apply Subtype.ext
  simpa only [Submodule.coe_add,Submodule.coe_sum,logSourceSupported,logInnerSupported,logShellSupported] using
    logSourceSchwartz_reconstruction W a V ha hV R haR hs b N hN

def sqrtShellSupported {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨sqrtShellSchwartz W a V ha hV hr hs b,(sqrtShellSchwartz_fixedSupport W a V ha hV hr hs b R haR).trans hb⟩

def sqrtInnerSupported {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨sqrtInnerSchwartz W a V ha hV hs b,(sqrtInnerSchwartz_fixedSupport W a V ha hV hs b R haR).trans hb⟩

def sqrtSourceSupported {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨sqrtSourceSchwartz W a V ha hV R haR hs b,(shiftedSqrtSource_support W a V s b R haR).trans hb⟩

lemma sqrtSupported_reconstruction {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K)
    (N : ℕ) (hN : R ≤ s*2^N) :
    sqrtSourceSupported W a V ha hV R haR K hs b hb =
      sqrtInnerSupported W a V ha hV R haR K hs b hb +
      ∑ j ∈ Finset.range N, sqrtShellSupported W a V ha hV R haR K
        (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b hb := by
  apply Subtype.ext
  simpa only [Submodule.coe_add,Submodule.coe_sum,sqrtSourceSupported,sqrtInnerSupported,sqrtShellSupported] using
    sqrtSourceSchwartz_reconstruction W a V ha hV R haR hs b N hN

end TamingCompatibility.HermitianRadial

end

end OAI
