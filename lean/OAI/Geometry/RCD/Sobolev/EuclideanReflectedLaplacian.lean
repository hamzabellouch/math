import OAI.Geometry.RCD.Sobolev.EuclideanConvolutionLaplacian

namespace OAI

/-! # Translation and reflection of compact Laplacian tests -/

open Set MeasureTheory InnerProductSpace Laplacian
open scoped ContDiff
noncomputable section
namespace RegularPointCoordinates

theorem scalar_reflection_directional {n : ℕ} {g : Euclidean n → ℝ}
    (hg : ContDiff ℝ 1 g) (a x v : Euclidean n) :
    fderiv ℝ (fun y => g (a-y)) x v = -fderiv ℝ g (a-x) v := by
  have he := (hg.differentiable (by norm_num) (a-x)).hasFDerivAt.comp x
    ((hasFDerivAt_const a x).sub (hasFDerivAt_id x))
  change (fderiv ℝ (g ∘ HSub.hSub a) x) v = _
  rw [he.fderiv]
  simp

theorem laplacian_comp_const_sub {n : ℕ} {g : Euclidean n → ℝ}
    (hg : ContDiff ℝ 2 g) (a : Euclidean n) :
    Δ (fun y => g (a-y)) = fun y => (Δ g) (a-y) := by
  have hcomp : ContDiff ℝ 2 (fun y => g (a-y)) := hg.comp (contDiff_const.sub contDiff_id)
  rw [laplacian_eq_sum_second_directional hcomp,laplacian_eq_sum_second_directional hg]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  let v : Euclidean n := EuclideanSpace.single i 1
  let dg := fun y => fderiv ℝ g y v
  have hdg : ContDiff ℝ 1 dg := (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
  have he : (fun y => fderiv ℝ (fun z => g (a-z)) y v)=(fun y => -dg (a-y)) := by
    funext y
    exact scalar_reflection_directional (hg.of_le (by norm_num)) a y v
  change fderiv ℝ (fun y => fderiv ℝ (fun z => g (a-z)) y v) x v=fderiv ℝ dg (a-x) v
  rw [he,fderiv_fun_neg]
  simp only [neg_apply]
  rw [scalar_reflection_directional hdg a x v,neg_neg]

end RegularPointCoordinates

end

end OAI
