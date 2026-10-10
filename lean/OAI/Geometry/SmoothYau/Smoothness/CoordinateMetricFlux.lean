import Mathlib
import OAI.Geometry.SmoothYau.Estimates.MixedPiolaDivergenceAbs

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
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def coordinateMetricFlux (b : Module.Basis ι ℝ E) (G : E → Matrix ι ι ℝ)
    (u : E → ℝ) (x : E) (i : ι) : ℝ :=
  Real.sqrt (G x).det * ∑ j, (G x)⁻¹ i j * fderiv ℝ u x (b j)

def coordinateMetricLaplacian (b : Module.Basis ι ℝ E) (G : E → Matrix ι ι ℝ)
    (u : E → ℝ) (x : E) : ℝ :=
  (Real.sqrt (G x).det)⁻¹ * ∑ i, fderiv ℝ (fun y => coordinateMetricFlux b G u y i) x (b i)

def pullbackMetricMatrix (b c : Module.Basis ι ℝ E) (G : E → Matrix ι ι ℝ)
    (f : E → E) (x : E) : Matrix ι ι ℝ :=
  (mixed_jacobianMatrix b c f x).transpose * G (f x) * mixed_jacobianMatrix b c f x

omit [FiniteDimensional ℝ E] in
lemma pullbackMetricMatrix_density (b c : Module.Basis ι ℝ E)
    (G : E → Matrix ι ι ℝ) (f : E → E) (x : E) :
    Real.sqrt (pullbackMetricMatrix b c G f x).det =
      |(mixed_jacobianMatrix b c f x).det| * Real.sqrt (G (f x)).det := by
  have he : (pullbackMetricMatrix b c G f x).det =
      (mixed_jacobianMatrix b c f x).det ^ 2 * (G (f x)).det := by
    simp only [pullbackMetricMatrix,Matrix.det_mul,Matrix.det_transpose]
    ring
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]

omit [FiniteDimensional ℝ E] in
lemma pullbackMetricMatrix_inverse_left (b c : Module.Basis ι ℝ E)
    (G : E → Matrix ι ι ℝ) (f : E → E) {x : E}
    (hx : IsUnit (mixed_jacobianMatrix b c f x).det) :
    (pullbackMetricMatrix b c G f x)⁻¹ * (mixed_jacobianMatrix b c f x).transpose =
      (mixed_jacobianMatrix b c f x)⁻¹ * (G (f x))⁻¹ := by
  have ht : IsUnit (mixed_jacobianMatrix b c f x).transpose.det := by
    simpa only [Matrix.det_transpose] using hx
  rw [pullbackMetricMatrix,Matrix.mul_inv_rev,Matrix.mul_inv_rev,
    Matrix.mul_assoc,Matrix.mul_assoc,Matrix.nonsing_inv_mul _ ht,
    Matrix.mul_one]

omit [FiniteDimensional ℝ E] in
lemma mixed_fderiv_comp_scalar {f : E → E} {u : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u (f x))
    (b c : Module.Basis ι ℝ E) (i : ι) :
    fderiv ℝ (u ∘ f) x (b i) =
      ∑ k, fderiv ℝ u (f x) (c k) * mixed_jacobianMatrix b c f x k i := by
  rw [fderiv_comp x hu hf,ContinuousLinearMap.comp_apply,
    ← c.sum_repr (fderiv ℝ f x (b i))]
  simp only [map_sum,map_smul,smul_eq_mul,mixed_jacobianMatrix_apply,
    Module.Basis.coord_apply,mul_comm]

omit [FiniteDimensional ℝ E] in
lemma coordinateMetricFlux_pullback {f : E → E} {u : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u (f x))
    (b c : Module.Basis ι ℝ E) (G : E → Matrix ι ι ℝ)
    (hx : IsUnit (mixed_jacobianMatrix b c f x).det) (i : ι) :
    coordinateMetricFlux b (pullbackMetricMatrix b c G f) (u ∘ f) x i =
      ∑ k, |(mixed_jacobianMatrix b c f x).det| * (mixed_jacobianMatrix b c f x)⁻¹ i k *
        coordinateMetricFlux c G u (f x) k := by
  let d : ι → ℝ := fun j => fderiv ℝ u (f x) (c j)
  have hh := congrArg (fun A : Matrix ι ι ℝ => A.mulVec d i)
    (pullbackMetricMatrix_inverse_left b c G f hx)
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec] at hh
  simp only [coordinateMetricFlux,mixed_fderiv_comp_scalar hf hu b c,
    pullbackMetricMatrix_density b c G f]
  have hs : (∑ j, (pullbackMetricMatrix b c G f x)⁻¹ i j *
      ∑ k, d k * mixed_jacobianMatrix b c f x k j) =
      ∑ k, (mixed_jacobianMatrix b c f x)⁻¹ i k * ∑ j, (G (f x))⁻¹ k j * d j := by
    simpa only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,mul_comm] using hh
  change (_ * _) * (∑ j, (pullbackMetricMatrix b c G f x)⁻¹ i j *
    ∑ k, d k * mixed_jacobianMatrix b c f x k j) = _
  rw [hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only [d]
  ring

omit [FiniteDimensional ℝ E] in
lemma differentiableAt_coordinateMetricFlux {u : E → ℝ} {G : E → Matrix ι ι ℝ}
    {x : E} (hu : ContDiffAt ℝ 2 u x) (hG : DifferentiableAt ℝ G x)
    (hx : 0 < (G x).det) (b : Module.Basis ι ℝ E) :
    DifferentiableAt ℝ (coordinateMetricFlux b G u) x := by
  have hd : DifferentiableAt ℝ (fun y => (G y).det) x :=
    (differentiable_det _).comp x hG
  have hi := differentiableAt_matrix_inv hG (isUnit_iff_ne_zero.mpr hx.ne')
  have hu' := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  apply differentiableAt_pi.mpr
  intro i
  apply (hd.sqrt hx.ne').mul
  apply DifferentiableAt.fun_sum
  intro j hj
  exact (differentiableAt_pi.mp (differentiableAt_pi.mp hi i) j).mul
    (hu'.clm_apply (differentiableAt_const _))

theorem coordinateMetricLaplacian_pullback {f : E → E} {u : E → ℝ}
    {G : E → Matrix ι ι ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hu : ContDiffAt ℝ 2 u (f x))
    (hG : DifferentiableAt ℝ G (f x)) (hpos : 0 < (G (f x)).det)
    (b c : Module.Basis ι ℝ E) (hx : IsUnit (mixed_jacobianMatrix b c f x).det) :
    coordinateMetricLaplacian b (pullbackMetricMatrix b c G f) (u ∘ f) x =
      coordinateMetricLaplacian c G u (f x) := by
  let J := mixed_jacobianMatrix b c f
  have hJ : ContinuousAt (fun y => (J y).det) x :=
    ((differentiable_det _).comp x (mixed_differentiableAt_jacobian hf b c)).continuousAt
  have hJn : ∀ᶠ y in 𝓝 x, IsUnit (J y).det := by
    filter_upwards [hJ.eventually_ne (isUnit_iff_ne_zero.mp hx)] with y hy
    exact isUnit_iff_ne_zero.mpr hy
  have huN : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u (f y) :=
    hf.continuousAt (hu.eventually (by simp))
  have hflux (i : ι) : (fun y => coordinateMetricFlux b (pullbackMetricMatrix b c G f) (u ∘ f) y i)
      =ᶠ[𝓝 x] (fun y => ∑ k, |(J y).det| * (J y)⁻¹ i k * coordinateMetricFlux c G u (f y) k) := by
    filter_upwards [hf.eventually (by simp),huN,hJn] with y hy hfyu hyJ
    exact coordinateMetricFlux_pullback (hy.differentiableAt (by norm_num))
      (hfyu.differentiableAt (by norm_num)) b c G hyJ i
  have hdiv := mixed_piola_divergence_abs hf (differentiableAt_coordinateMetricFlux hu hG hpos c) b c hx
  simp only [coordinateMetricLaplacian]
  simp_rw [(hflux _).fderiv_eq]
  rw [pullbackMetricMatrix_density,hdiv]
  have hn : |(J x).det| ≠ 0 := abs_ne_zero.mpr (isUnit_iff_ne_zero.mp hx)
  change (_ * _)⁻¹ * (|(J x).det| * _) = _
  rw [_root_.mul_inv_rev]
  change (Real.sqrt (G (f x)).det)⁻¹ * (|(J x).det|)⁻¹ * (|(J x).det| * _) = _
  rw [mul_assoc,inv_mul_cancel_left₀ hn]
end YauCounterexamples

end

end OAI
