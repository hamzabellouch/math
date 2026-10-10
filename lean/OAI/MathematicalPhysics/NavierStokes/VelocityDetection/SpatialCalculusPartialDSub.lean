import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialCalculus

namespace OAI

noncomputable section
namespace VelocityDetection.SpatialCalculus
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators

theorem partialD_sub {n : ℕ} (i : Fin n) {f g : Coord n → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    partialD i (fun X => f X - g X) = fun X => partialD i f X - partialD i g X := by
  funext X
  change partialD i (f - g) X = partialD i f X - partialD i g X
  simp only [partialD_eq_fderiv i (hf.sub hg), partialD_eq_fderiv i hf, partialD_eq_fderiv i hg]
  rw [fderiv_sub (hf X) (hg X)]
  rfl

theorem laplacian_sub {n : ℕ} {f g : Coord n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (X : Coord n) :
    laplacian (fun _ Y => f Y - g Y) 0 X =
      laplacian (fun _ => f) 0 X - laplacian (fun _ => g) 0 X := by
  change (∑ i : Fin n, partialD i (partialD i (fun Y => f Y - g Y)) X) = _
  simp_rw [partialD_sub _ (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))]
  simp_rw [partialD_sub _ ((contDiff_partialD _ hf).differentiable (by norm_num))
    ((contDiff_partialD _ hg).differentiable (by norm_num)), Finset.sum_sub_distrib]
  rfl

end VelocityDetection.SpatialCalculus
end

end OAI
