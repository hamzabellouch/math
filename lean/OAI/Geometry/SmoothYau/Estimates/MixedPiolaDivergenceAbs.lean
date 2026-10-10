import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.MixedPiolaIdentity
import OAI.Geometry.SmoothYau.Smoothness.PiolaIdentity

namespace OAI

noncomputable section
namespace YauCounterexamples
section
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] in
lemma local_abs_multiplier {d : E → ℝ} {x : E} (hd : ContinuousAt d x) (hx : d x ≠ 0) :
    ∃ c : ℝ, |d x| = c * d x ∧ ∀ᶠ y in 𝓝 x, |d y| = c * d y := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · refine ⟨-1, by rw [abs_of_neg hn]; ring, ?_⟩
    filter_upwards [hd.eventually_lt continuousAt_const hn] with y hy
    rw [abs_of_neg hy]
    ring
  · refine ⟨1, by rw [abs_of_pos hp, one_mul], ?_⟩
    filter_upwards [continuousAt_const.eventually_lt hd hp] with y hy
    rw [abs_of_pos hy, one_mul]

lemma piola_divergence_abs {f : E → E} {X : E → ι → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hX : DifferentiableAt ℝ X (f x))
    (b : Module.Basis ι ℝ E) (hx : IsUnit (jacobianMatrix b f x).det) :
    ∑ i, fderiv ℝ (fun y => ∑ k, |(jacobianMatrix b f y).det| *
      (jacobianMatrix b f y)⁻¹ i k * X (f y) k) x (b i) =
      |(jacobianMatrix b f x).det| * ∑ k, fderiv ℝ (fun z => X z k) (f x) (b k) := by
  let J := jacobianMatrix b f
  have hJ : DifferentiableAt ℝ J x := differentiableAt_jacobian hf b
  have hd : ContinuousAt (fun y => (J y).det) x :=
    ((differentiable_det _).comp x hJ).continuousAt
  obtain ⟨c, hcx, hcy⟩ := local_abs_multiplier hd (isUnit_iff_ne_zero.mp hx)
  have hh (i : ι) : fderiv ℝ (fun y => ∑ k, |(J y).det| * (J y)⁻¹ i k * X (f y) k) x =
      c • fderiv ℝ (fun y => ∑ k, (J y).det * (J y)⁻¹ i k * X (f y) k) x := by
    have he : (fun y => ∑ k, |(J y).det| * (J y)⁻¹ i k * X (f y) k) =ᶠ[𝓝 x]
        (fun y => c * ∑ k, (J y).det * (J y)⁻¹ i k * X (f y) k) := by
      filter_upwards [hcy] with y hy
      simp only [hy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [he.fderiv_eq]
    have hf' := hf.differentiableAt (by norm_num)
    have hB := differentiableAt_matrix_inv hJ hx
    have hd' : DifferentiableAt ℝ (fun y => (J y).det) x :=
      (differentiable_det _).comp x hJ
    exact fderiv_const_mul (DifferentiableAt.fun_sum (fun k _ =>
      (hd'.mul (differentiableAt_pi.mp (differentiableAt_pi.mp hB i) k)).mul
        ((differentiableAt_pi.mp hX k).comp x hf'))) c
  change (∑ i, fderiv ℝ (fun y => ∑ k, |(J y).det| * (J y)⁻¹ i k * X (f y) k) x (b i)) = _
  simp_rw [hh, _root_.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, piola_divergence hf hX b hx]
  change c * ((J x).det * _) = |(J x).det| * _
  rw [hcx, mul_assoc]

end

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma mixed_piola_divergence_abs {f : E → E} {X : E → ι → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hX : DifferentiableAt ℝ X (f x))
    (b c : Module.Basis ι ℝ E) (hx : IsUnit (mixed_jacobianMatrix b c f x).det) :
    ∑ i, fderiv ℝ (fun y => ∑ k, |(mixed_jacobianMatrix b c f y).det| *
      (mixed_jacobianMatrix b c f y)⁻¹ i k * X (f y) k) x (b i) =
      |(mixed_jacobianMatrix b c f x).det| * ∑ k, fderiv ℝ (fun z => X z k) (f x) (c k) := by
  let J := mixed_jacobianMatrix b c f
  have hJ : DifferentiableAt ℝ J x := mixed_differentiableAt_jacobian hf b c
  have hd : ContinuousAt (fun y => (J y).det) x :=
    ((differentiable_det _).comp x hJ).continuousAt
  obtain ⟨sgn, hcx, hcy⟩ := local_abs_multiplier hd (isUnit_iff_ne_zero.mp hx)
  have hh (i : ι) : fderiv ℝ (fun y => ∑ k, |(J y).det| * (J y)⁻¹ i k * X (f y) k) x =
      sgn • fderiv ℝ (fun y => ∑ k, (J y).det * (J y)⁻¹ i k * X (f y) k) x := by
    have he : (fun y => ∑ k, |(J y).det| * (J y)⁻¹ i k * X (f y) k) =ᶠ[𝓝 x]
        (fun y => sgn * ∑ k, (J y).det * (J y)⁻¹ i k * X (f y) k) := by
      filter_upwards [hcy] with y hy
      simp only [hy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [he.fderiv_eq]
    have hf' := hf.differentiableAt (by norm_num)
    have hB := differentiableAt_matrix_inv hJ hx
    have hd' : DifferentiableAt ℝ (fun y => (J y).det) x :=
      (differentiable_det _).comp x hJ
    exact fderiv_const_mul (DifferentiableAt.fun_sum (fun k _ =>
      (hd'.mul (differentiableAt_pi.mp (differentiableAt_pi.mp hB i) k)).mul
        ((differentiableAt_pi.mp hX k).comp x hf'))) sgn
  change (∑ i, fderiv ℝ (fun y => ∑ k, |(J y).det| * (J y)⁻¹ i k * X (f y) k) x (b i)) = _
  simp_rw [hh, _root_.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, mixed_piola_divergence hf hX b c hx]
  change sgn * ((J x).det * _) = |(J x).det| * _
  rw [hcx, mul_assoc]



end YauCounterexamples
end

end OAI
