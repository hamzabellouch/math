import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Compact

namespace OAI

/-! Pointwise calculus on the compact path space used in the local flow proof.
The continuous linear map below lifts a continuously varying linear map to
continuous paths.  No differential-equation hypothesis is used here. -/

noncomputable section
namespace ForcedComputation.Flow

open Set Filter
open scoped Topology ContDiff

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Apply a continuous family of linear maps pointwise to a path. -/
def applyPath (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩
      map_add' := by
        intro u v
        ext t
        change A t (u t + v t) = A t (u t) + A t (v t)
        exact map_add (A t) (u t) (v t)
      map_smul' := by
        intro c u
        ext t
        change A t (c • u t) = c • A t (u t)
        exact map_smul (A t) c (u t) }
    ‖A‖ (by
      intro u
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
      intro t
      exact ((A t).le_opNorm (u t)).trans
        (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
          (norm_nonneg _) (norm_nonneg _)))

@[simp] theorem applyPath_apply (A : C(K, E →L[ℝ] F)) (u : C(K, E)) (t : K) :
    applyPath A u t = A t (u t) := rfl

theorem applyPath_norm (A : C(K, E →L[ℝ] F)) : ‖applyPath A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

/-- Pointwise application depends continuously and linearly on the family. -/
def applyPathL : C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
  LinearMap.mkContinuous
    { toFun := fun A : C(K, E →L[ℝ] F) => applyPath A
      map_add' := by
        intro A B
        ext u t
        change (A t + B t) (u t) = A t (u t) + B t (u t)
        exact add_apply _ _ _
      map_smul' := by
        intro c A
        ext u t
        rfl }
    1 (by
      intro A
      change ‖applyPath A‖ ≤ (1 : ℝ) * ‖A‖
      rw [one_mul]
      exact applyPath_norm A)

@[simp] theorem applyPathL_apply (A : C(K, E →L[ℝ] F)) :
    applyPathL A = applyPath A := rfl

/-- A uniform derivative modulus bounds the first-order remainder on a segment. -/
theorem remainder_bound {f : E → F} {df : E → E →L[ℝ] F}
    (hf : ∀ z, HasFDerivAt f (df z) z) (x y : E) {ε : ℝ}
    (hε : ∀ z ∈ segment ℝ x y, ‖df z - df x‖ ≤ ε) :
    ‖f y - f x - df x (y - x)‖ ≤ ε * ‖y - x‖ := by
  have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => f z - df x z) (f' := fun z => df z - df x)
    (fun z _ => ((hf z).sub (df x).hasFDerivAt).hasFDerivWithinAt)
    hε (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have he : (f y - df x y) - (f x - df x x) = f y - f x - df x (y - x) := by
    rw [map_sub]
    abel
  rwa [he] at h

end ForcedComputation.Flow

end

end OAI
