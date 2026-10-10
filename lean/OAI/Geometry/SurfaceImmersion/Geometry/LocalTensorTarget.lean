import OAI.Geometry.SurfaceImmersion.Correction.WeightedPolynomialBounds
import OAI.Geometry.Immersion.ClosedSurface.MeanSupport
import OAI.Geometry.SurfaceImmersion.Correction.PrimitiveMeanStep

namespace OAI

/-! Extend the local primitive target around its reference tensor. The
cutoff keeps both the global trial ball and the slow derivative bounds. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PrimitiveRealization
open WeightedEstimates PhaseMean

def localTensorTarget (χ : SmallModes.Base → ℝ)
    (reference target : SmallModes.Base → Tensor) : SmallModes.Base → Tensor :=
  fun x => reference x+χ x • (target x-reference x)

lemma localTensorTarget_smooth {χ : SmallModes.Base → ℝ}
    {reference target : SmallModes.Base → Tensor}
    (hχ : ContDiff ℝ ∞ χ) (hr : ContDiff ℝ ∞ reference) (ht : ContDiff ℝ ∞ target) :
    ContDiff ℝ ∞ (localTensorTarget χ reference target) := hr.add (hχ.smul (ht.sub hr))

lemma localTensorTarget_eq {χ : SmallModes.Base → ℝ}
    {reference target : SmallModes.Base → Tensor} {x : SmallModes.Base} (hχ : χ x = 1) :
    localTensorTarget χ reference target x = target x := by
  simp only [localTensorTarget,hχ,one_smul,add_sub_cancel]

lemma localTensorTarget_distance {U : Set SmallModes.Base} {χ : SmallModes.Base → ℝ}
    {reference target : SmallModes.Base → Tensor} {r : ℝ} (hr : 0 ≤ r)
    (hχ : ∀ x, |χ x| ≤ 1) (hsp : tsupport χ ⊆ U)
    (ht : ∀ x ∈ U, ‖target x-reference x‖ ≤ r) (x : SmallModes.Base) :
    ‖localTensorTarget χ reference target x-reference x‖ ≤ r := by
  simp only [localTensorTarget,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
  by_cases hz : χ x = 0
  · simpa only [hz,abs_zero,zero_mul] using hr
  · have hx : x ∈ U := hsp (subset_tsupport χ (Function.mem_support.mpr hz))
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχ x)).trans (ht x hx)

lemma localTensorTarget_bound {U : Set SmallModes.Base} (hU : IsOpen U)
    {χ : SmallModes.Base → ℝ} {reference target : SmallModes.Base → Tensor}
    (hχ : ContDiff ℝ ∞ χ) (hr : ContDiff ℝ ∞ reference) (ht : ContDiff ℝ ∞ target)
    (hsp : tsupport χ ⊆ U) {s A B C : ℝ} {m : ℕ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hχb : WeightedBound univ 1 m C χ)
    (hrb : WeightedBound univ s m A reference)
    (htb : WeightedBound U s m B (target-reference)) :
    WeightedBound univ s m (A+2^m*C*B) (localTensorTarget χ reference target) := by
  have hχU := ((hχb.shrink_scale hs hs1).restrict_open hU)
  have hb := hχU.smul_real hU.uniqueDiffOn hs hC hB hχ.contDiffOn (ht.sub hr).contDiffOn htb
  have hb' := hb.extend_support hU ((tsupport_smul_subset_left χ (target-reference)).trans hsp)
    (by positivity)
  exact hrb.add isOpen_univ.uniqueDiffOn hs hr.contDiffOn (hχ.smul (ht.sub hr)).contDiffOn hb'

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
