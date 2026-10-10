import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.FderivCofactorApply

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def mixed_jacobianMatrix (b c : Module.Basis ι ℝ E) (f : E → E) (x : E) : Matrix ι ι ℝ :=
  LinearMap.toMatrix b c (fderiv ℝ f x).toLinearMap

omit [FiniteDimensional ℝ E] in
lemma mixed_jacobianMatrix_apply (b c : Module.Basis ι ℝ E) (f : E → E) (x : E) (i j : ι) :
    mixed_jacobianMatrix b c f x i j = c.coord i (fderiv ℝ f x (b j)) := by
  simp only [mixed_jacobianMatrix, LinearMap.toMatrix_apply, Module.Basis.coord_apply,
    ContinuousLinearMap.coe_coe]

lemma mixed_differentiableAt_jacobian {f : E → E} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (b c : Module.Basis ι ℝ E) :
    DifferentiableAt ℝ (mixed_jacobianMatrix b c f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  let L : E →L[ℝ] ℝ := (c.coord i).toContinuousLinearMap
  simp only [mixed_jacobianMatrix_apply]
  change DifferentiableAt ℝ (fun y => L (fderiv ℝ f y (b j))) x
  exact L.differentiableAt.comp x (hd.clm_apply (differentiableAt_const _))

lemma mixed_fderiv_jacobian_apply {f : E → E} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (b c : Module.Basis ι ℝ E) (v : E) (i j : ι) :
    fderiv ℝ (mixed_jacobianMatrix b c f) x v i j =
      c.coord i (fderiv ℝ (fderiv ℝ f) x v (b j)) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [fderiv_matrix_apply (mixed_differentiableAt_jacobian hf b c)]
  let L : E →L[ℝ] ℝ := (c.coord i).toContinuousLinearMap
  simp only [mixed_jacobianMatrix_apply]
  change fderiv ℝ (fun y => L (fderiv ℝ f y (b j))) x v = _
  rw [show (fun y => L (fderiv ℝ f y (b j))) =
      L ∘ (fun y => fderiv ℝ f y (b j)) from rfl,
    fderiv_comp x L.differentiableAt (hd.clm_apply (differentiableAt_const _)),
    L.fderiv, fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  rfl

lemma mixed_jacobian_curl {f : E → E} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (b c : Module.Basis ι ℝ E) (i l m : ι) :
    fderiv ℝ (mixed_jacobianMatrix b c f) x (b i) l m =
      fderiv ℝ (mixed_jacobianMatrix b c f) x (b m) l i := by
  rw [mixed_fderiv_jacobian_apply hf, mixed_fderiv_jacobian_apply hf,
    (hf.isSymmSndFDerivAt (by norm_num)).eq]
end YauCounterexamples

end

end OAI
