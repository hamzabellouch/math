import Mathlib.Analysis.Calculus.MeanValue
import OAI.Geometry.NodalSets.Charts.CorrugationFrameBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_convex_freezing (f : Coord → F) {D : Set Coord}
    (hD : IsCompact D) (hconv : Convex ℝ D)
    (hdiff : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hder : ContinuousOn (fderiv ℝ f) D) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ D, ∀ y ∈ D, ‖f x-f y‖ ≤ C*‖x-y‖ := by
  obtain ⟨C,hC,hbound⟩ := (hD.image_of_continuousOn hder).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro x hx y hy
  exact hconv.norm_image_sub_le_of_norm_fderiv_le hdiff
    (fun z hz ↦ hbound _ ⟨z,hz,rfl⟩) hy hx

lemma smooth_compact_freezing (f : Coord → F) {D U : Set Coord}
    (hD : IsCompact D) (hconv : Convex ℝ D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ D, ∀ y ∈ D, ‖f x-f y‖ ≤ C*‖x-y‖ := by
  have hat : ∀ x ∈ D, ContDiffAt ℝ ∞ f x :=
    fun x hx ↦ hf.contDiffAt (hU.mem_nhds (hDU hx))
  apply compact_convex_freezing f hD hconv
  · exact fun x hx ↦ (hat x hx).differentiableAt (by simp)
  · intro x hx
    exact ((hat x hx).continuousAt_fderiv (by simp)).continuousWithinAt

lemma smooth_compact_covector_freezing (S : Coord → ℝ) {D U : Set Coord}
    (hD : IsCompact D) (hconv : Convex ℝ D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hS : ContDiffOn ℝ ∞ S U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ D, ∀ y ∈ D, ∀ v : Coord,
      |fderiv ℝ S x v-fderiv ℝ S y v| ≤ C*‖x-y‖*‖v‖ := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ S) U :=
    hS.fderiv_of_isOpen hU (by simp)
  obtain ⟨C,hC,hb⟩ := smooth_compact_freezing (fderiv ℝ S) hD hconv hU hDU hd
  refine ⟨C,hC,?_⟩
  intro x hx y hy v
  exact ((fderiv ℝ S x-fderiv ℝ S y).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hb x hx y hy) (norm_nonneg v))

end
end Yau.Geometry

end OAI
