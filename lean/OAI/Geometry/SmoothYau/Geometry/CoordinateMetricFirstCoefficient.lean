import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.CoordinateMetricFlux

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
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def coordinateMetricFirstCoefficient (b : Module.Basis ι ℝ E)
    (G : E → Matrix ι ι ℝ) (x : E) (j : ι) : ℝ :=
  (Real.sqrt (G x).det)⁻¹ * ∑ i, fderiv ℝ (fun y => Real.sqrt (G y).det * (G y)⁻¹ i j) x (b i)

omit [FiniteDimensional ℝ E] in
lemma coordinateMetricLaplacian_expansion (b : Module.Basis ι ℝ E)
    {G : E → Matrix ι ι ℝ} {u : E → ℝ} {x : E}
    (hG : DifferentiableAt ℝ G x) (hu : ContDiffAt ℝ 2 u x) (hp : 0 < (G x).det) :
    coordinateMetricLaplacian b G u x =
      (∑ i, ∑ j, (G x)⁻¹ i j * fderiv ℝ (fun y => fderiv ℝ u y (b j)) x (b i)) +
        ∑ j, coordinateMetricFirstCoefficient b G x j * fderiv ℝ u x (b j) := by
  let ρ := fun y => Real.sqrt (G y).det
  have hρ : DifferentiableAt ℝ ρ x := ((differentiable_det _).comp x hG).sqrt hp.ne'
  have hAi := differentiableAt_matrix_inv hG (isUnit_iff_ne_zero.mpr hp.ne')
  have hA (i j : ι) : DifferentiableAt ℝ (fun y => (G y)⁻¹ i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hAi i) j
  have hv := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he (i : ι) : (fun y => coordinateMetricFlux b G u y i) =
      fun y => ∑ j, (ρ y * (G y)⁻¹ i j) * fderiv ℝ u y (b j) := by
    funext y
    simp only [coordinateMetricFlux,ρ,Finset.mul_sum,mul_assoc]
  have hder (i : ι) : fderiv ℝ (fun y => coordinateMetricFlux b G u y i) x (b i) =
      ∑ j, ((ρ x * (G x)⁻¹ i j) * fderiv ℝ (fun y => fderiv ℝ u y (b j)) x (b i) +
        fderiv ℝ u x (b j) * fderiv ℝ (fun y => ρ y * (G y)⁻¹ i j) x (b i)) := by
    rw [he]
    erw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j y => (ρ y * (G y)⁻¹ i j) * fderiv ℝ u y (b j))
      (fun j _ => (hρ.mul (hA i j)).mul (hv.clm_apply (differentiableAt_const _)))]
    simp only [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    erw [fderiv_mul (c := fun y => ρ y * (G y)⁻¹ i j)
      (d := fun y => fderiv ℝ u y (b j)) (hρ.mul (hA i j))
      (hv.clm_apply (differentiableAt_const _))]
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  change (ρ x)⁻¹ * ∑ i, fderiv ℝ (fun y => coordinateMetricFlux b G u y i) x (b i) = _
  simp_rw [hder,Finset.sum_add_distrib]
  rw [mul_add,Finset.mul_sum,Finset.mul_sum]
  have hn : ρ x ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hmain : (∑ i, (ρ x)⁻¹ * ∑ j, ρ x * (G x)⁻¹ i j *
      fderiv ℝ (fun y => fderiv ℝ u y (b j)) x (b i)) =
      ∑ i, ∑ j, (G x)⁻¹ i j * fderiv ℝ (fun y => fderiv ℝ u y (b j)) x (b i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [hmain]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [coordinateMetricFirstCoefficient,ρ,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end YauCounterexamples
end

end OAI
