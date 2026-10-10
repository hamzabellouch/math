import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open scoped ContDiff

def smoothScalarAlgebra (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Subalgebra ℝ (E → ℝ) where
  carrier := {f | ContDiff ℝ (↑(⊤ : ℕ∞)) f}
  algebraMap_mem' r := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : E => r)
    exact contDiff_const
  zero_mem' := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : E => 0)
    exact contDiff_const
  one_mem' := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : E => 1)
    exact contDiff_const
  add_mem' hf hg := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) _ at hf hg ⊢
    exact hf.add hg
  mul_mem' hf hg := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) _ at hf hg ⊢
    exact hf.mul hg

abbrev SmoothScalar (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  smoothScalarAlgebra E

theorem smoothScalar_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SmoothScalar E) : ContDiff ℝ (↑(⊤ : ℕ∞)) f.val := by
  exact f.property

def smoothDirection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) : SmoothScalar E →ₗ[ℝ] SmoothScalar E where
  toFun f := ⟨fun x => fderiv ℝ f.val x v, by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) _
    exact ((smoothScalar_contDiff f).fderiv_right
      (m := ↑(⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    change fderiv ℝ (f.val + g.val) x v = fderiv ℝ f.val x v + fderiv ℝ g.val x v
    rw [fderiv_add ((smoothScalar_contDiff f).differentiable (by simp) x)
      ((smoothScalar_contDiff g).differentiable (by simp) x)]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change fderiv ℝ (c • f.val) x v = c • fderiv ℝ f.val x v
    rw [fderiv_const_smul ((smoothScalar_contDiff f).differentiable (by simp) x)]
    rfl

@[simp] theorem smoothDirection_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (f : SmoothScalar E) (x : E) :
    (smoothDirection v f).val x = fderiv ℝ f.val x v := rfl

theorem smoothDirection_comm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v w : E) (f : SmoothScalar E) :
    smoothDirection v (smoothDirection w f) =
      smoothDirection w (smoothDirection v f) := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (fun y => fderiv ℝ f.val y w) x v =
    fderiv ℝ (fun y => fderiv ℝ f.val y v) x w
  have hd : DifferentiableAt ℝ (fderiv ℝ f.val) x :=
    ((smoothScalar_contDiff f).fderiv_right (m := ↑(⊤ : ℕ∞)) (by simp)).differentiable (by simp) x
  rw [fderiv_clm_apply hd (differentiableAt_const w),
    fderiv_clm_apply hd (differentiableAt_const v)]
  simpa using ((smoothScalar_contDiff f).contDiffAt.isSymmSndFDerivAt (by simp) v w)

end ScalarConductivity

end

end OAI
