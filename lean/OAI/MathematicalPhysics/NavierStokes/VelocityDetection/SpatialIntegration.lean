import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialCalculus
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivatives

namespace OAI

noncomputable section
namespace VelocityDetection.SpatialCalculus
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators

theorem integral_partialD_eq_zero {n : ℕ} (i : Fin n) {f : Coord n → ℝ}
    (hf : Differentiable ℝ f) (hfi : Integrable f) (hdi : Integrable (partialD i f)) :
    (∫ X, partialD i f X) = 0 := by
  have hdi' : Integrable (fun X => fderiv ℝ f X (Pi.single i 1)) := by
    change Integrable (fun X => partialD i f X) at hdi
    simpa only [partialD_eq_fderiv i hf] using hdi
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : Coord n => (1 : ℝ)) (g := f) (v := Pi.single i 1)
    (by simp)
    (by simpa using hdi') (by simpa using hfi)
    (fun _ _ => differentiableAt_const 1) (fun X _ => hf X)
  simpa only [partialD_eq_fderiv i hf, fderiv_const_apply, zero_apply,
    one_mul, zero_mul, integral_zero, neg_zero] using h

theorem integral_laplacian_eq_zero {n : ℕ} {f : Coord n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hi : ∀ i, Integrable (partialD i f))
    (hii : ∀ i, Integrable (partialD i (partialD i f))) :
    (∫ X, laplacian (fun _ => f) 0 X) = 0 := by
  change (∫ X, ∑ i, partialD i (partialD i f) X) = 0
  rw [integral_finsetSum _ (fun i _ => hii i)]
  simp_rw [integral_partialD_eq_zero _
    ((contDiff_partialD _ hf).differentiable (by norm_num)) (hi _) (hii _)]
  simp

theorem integral_transport_eq_zero {n : ℕ} {f : Coord n → ℝ} {a : Coord n → Coord n}
    (hf : ContDiff ℝ 1 f) (ha : ∀ i, ContDiff ℝ 1 (fun X => a X i))
    (hac : ∀ i, HasCompactSupport (fun X => a X i))
    (hdiv : ∀ X, (∑ i, partialD i (fun Y => a Y i) X) = 0) :
    (∫ X, ∑ i, a X i * partialD i f X) = 0 := by
  have hi (i : Fin n) : Integrable (fun X => a X i * partialD i f X) :=
    ((ha i).continuous.mul (continuous_partialD i hf)).integrable_of_hasCompactSupport
      (hac i).mul_right
  have hi' (i : Fin n) : Integrable (fun X => partialD i (fun Y => a Y i) X * f X) :=
    ((continuous_partialD i (ha i)).mul hf.continuous).integrable_of_hasCompactSupport
      (compactSupport_partialD i ((ha i).differentiable (by norm_num)) (hac i)).mul_right
  calc
    _ = ∑ i, ∫ X, a X i * partialD i f X := integral_finsetSum _ (fun i _ => hi i)
    _ = -∑ i, ∫ X, partialD i (fun Y => a Y i) X * f X := by
      simp only [integral_mul_partialD _ (ha _) hf (hac _), Finset.sum_neg_distrib]
    _ = -(∫ X, (∑ i, partialD i (fun Y => a Y i) X) * f X) := by
      simp only [Finset.sum_mul, integral_finsetSum _ (fun i _ => hi' i)]
    _ = 0 := by simp only [hdiv, zero_mul, integral_zero, neg_zero]

theorem scalar_mass_rate {n : ℕ} {f r g : Coord n → ℝ} {a : Coord n → Coord n} {ν : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hi : ∀ i, Integrable (partialD i f))
    (hii : ∀ i, Integrable (partialD i (partialD i f)))
    (hg : Integrable g) (ha : ∀ i, ContDiff ℝ 1 (fun X => a X i))
    (hac : ∀ i, HasCompactSupport (fun X => a X i))
    (hdiv : ∀ X, (∑ i, partialD i (fun Y => a Y i) X) = 0)
    (heq : ∀ X, r X + (∑ i, a X i * partialD i f X) =
      ν * laplacian (fun _ => f) 0 X + g X) :
    (∫ X, r X) = ∫ X, g X := by
  have hd : Integrable (fun X => laplacian (fun _ => f) 0 X) :=
    integrable_finsetSum _ (fun i _ => hii i)
  have ht : Integrable (fun X => ∑ i, a X i * partialD i f X) :=
    integrable_finsetSum _ (fun i _ =>
      ((ha i).continuous.mul (continuous_partialD i (hf.of_le (by norm_num))))
        |>.integrable_of_hasCompactSupport (hac i).mul_right)
  have hr : r = fun X => ν * laplacian (fun _ => f) 0 X + g X -
      (∑ i, a X i * partialD i f X) := funext (fun X => by linarith [heq X])
  rw [hr, integral_sub (f := fun X => ν * laplacian (fun _ => f) 0 X + g X)
    ((hd.const_mul ν).add hg) ht,
    integral_add (hd.const_mul ν) hg, integral_const_mul,
    integral_laplacian_eq_zero hf hi hii,
    integral_transport_eq_zero (hf.of_le (by norm_num)) ha hac hdiv]
  ring

end VelocityDetection.SpatialCalculus
end

end OAI
