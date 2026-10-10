import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import OAI.Geometry.NodalSets.Elliptic.SmoothBilinearPullback

namespace OAI

namespace Yau.Geometry
open Manifold ContinuousLinearMap
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

local notation "F" => EuclideanSpace ℝ (Fin 5)
local notation "W" => ℂ

def warpedAmbientForm (B : F →L[ℝ] F →L[ℝ] ℝ) (q : ℝ) :
    (F × W) →L[ℝ] (F × W) →L[ℝ] ℝ :=
  bilinearPullback B (fst ℝ F W) + q^2 • bilinearPullback (innerSL ℝ) (snd ℝ F W)

lemma warpedAmbientForm_apply (B : F →L[ℝ] F →L[ℝ] ℝ) (q : ℝ) (v w : F × W) :
    warpedAmbientForm B q v w = B v.1 w.1 + q^2 * inner ℝ v.2 w.2 := rfl

lemma warpedAmbientForm_smooth (B : M → F →L[ℝ] F →L[ℝ] ℝ) (q : M → ℝ)
    (hB : ContMDiff I 𝓘(ℝ,F →L[ℝ] F →L[ℝ] ℝ) ∞ B)
    (hq : ContMDiff I 𝓘(ℝ,ℝ) ∞ q) :
    ContMDiff I 𝓘(ℝ,(F × W) →L[ℝ] (F × W) →L[ℝ] ℝ) ∞
      (fun x ↦ warpedAmbientForm (B x) (q x)) := by
  unfold warpedAmbientForm bilinearPullback
  exact (contMDiff_const.clm_comp (hB.clm_comp contMDiff_const)).add
    (((contDiff_id.pow 2).contMDiff.comp hq).smul contMDiff_const)

lemma warpedAmbientForm_symm (B : F →L[ℝ] F →L[ℝ] ℝ) (q : ℝ)
    (hs : ∀ v w, B v w = B w v) (v w : F × W) :
    warpedAmbientForm B q v w = warpedAmbientForm B q w v := by
  simp only [warpedAmbientForm_apply,hs v.1 w.1,real_inner_comm v.2 w.2]

lemma warpedAmbientForm_pos (B : F →L[ℝ] F →L[ℝ] ℝ) {q : ℝ}
    (hp : ∀ v, v ≠ 0 → 0 < B v v) (hq : 0 < q)
    (v : F × W) (hv : v ≠ 0) : 0 < warpedAmbientForm B q v v := by
  rw [warpedAmbientForm_apply,real_inner_self_eq_norm_sq]
  by_cases h : v.1 = 0
  · have h2 : v.2 ≠ 0 := fun hz ↦ hv (Prod.ext h hz)
    simp only [h,map_zero,zero_add]
    exact mul_pos (sq_pos_of_pos hq) (sq_pos_of_pos (norm_pos_iff.mpr h2))
  · exact add_pos_of_pos_of_nonneg (hp _ h) (mul_nonneg (sq_nonneg q) (sq_nonneg ‖v.2‖))

end
end Yau.Geometry

end OAI
