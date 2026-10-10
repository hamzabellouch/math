import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusScalarInput

namespace OAI

/-! The diffusion and incompressible transport terms have zero spatial
integral on the unit torus. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set MeasureTheory
open scoped ContDiff BigOperators

theorem spatialD_periodic {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g)
    (hp : PlanePeriodic g) (j : Fin 2) : PlanePeriodic (spatialD j g) := by
  intro x n
  have h := fderiv_translation (hg.differentiable (by simp)) (fun y => hp y n) x
  exact congrArg (fun A : Plane →L[ℝ] ℝ => A (PlanarHamiltonian.basis j)) h

theorem scalarLaplacian_integral_zero {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g)
    (hp : PlanePeriodic g) :
    (∫ x in Icc (0 : Plane) (fun _ => 1), scalarLaplacian g x) = 0 := by
  unfold scalarLaplacian
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j _
    exact integral_planar_periodic_derivative (spatialD_smooth j hg) (spatialD_periodic hg hp j) j
  · intro j _
    exact (spatialD_smooth j (spatialD_smooth j hg)).continuous.integrableOn_Icc

theorem scalar_directional_basis (g : Plane → ℝ) (x v : Plane) :
    fderiv ℝ g x v = ∑ j : Fin 2, v j * spatialD j g x := by
  have hv : v = v 0 • PlanarHamiltonian.basis 0 + v 1 • PlanarHamiltonian.basis 1 := by
    ext j
    fin_cases j <;> simp
  rw [hv, map_add, map_smul, map_smul, Fin.sum_univ_two]
  simp only [spatialD, smul_eq_mul]
  congr 1 <;> simp

theorem divergence_scalar_product {a : Plane → Plane} {g : Plane → ℝ}
    (ha : ContDiff ℝ ∞ a) (hg : ContDiff ℝ ∞ g) (x : Plane) :
    PlanarHamiltonian.divergence (fun y => g y • a y) x =
      g x * PlanarHamiltonian.divergence a x + fderiv ℝ g x (a x) := by
  have hd (j : Fin 2) : spatialD j (fun y => (g y • a y) j) x =
      g x * spatialD j (fun y => a y j) x + a x j * spatialD j g x := by
    have h := ((hg.differentiable (by simp) x).hasFDerivAt).mul
      (((contDiff_apply ℝ ℝ j).comp ha).differentiable (by simp) x).hasFDerivAt
    change HasFDerivAt (fun y => (g y • a y) j) _ x at h
    rw [spatialD, h.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, spatialD, Function.comp_def]
  rw [PlanarHamiltonian.divergence, scalar_directional_basis]
  simp_rw [hd]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

theorem divergence_periodic_integral_zero {a : Plane → Plane}
    (ha : ContDiff ℝ ∞ a) (hp : PlanePeriodic a) :
    (∫ x in Icc (0 : Plane) (fun _ => 1), PlanarHamiltonian.divergence a x) = 0 := by
  unfold PlanarHamiltonian.divergence
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j _
    exact integral_planar_periodic_derivative ((contDiff_apply ℝ ℝ j).comp ha)
      (fun x n => congrFun (hp x n) j) j
  · intro j _
    exact (spatialD_smooth j ((contDiff_apply ℝ ℝ j).comp ha)).continuous.integrableOn_Icc

theorem scalar_transport_integral_zero {a : Plane → Plane} {g : Plane → ℝ}
    (ha : ContDiff ℝ ∞ a) (hg : ContDiff ℝ ∞ g)
    (hpa : PlanePeriodic a) (hpg : PlanePeriodic g)
    (hdiv : ∀ x, PlanarHamiltonian.divergence a x = 0) :
    (∫ x in Icc (0 : Plane) (fun _ => 1), fderiv ℝ g x (a x)) = 0 := by
  have hp : PlanePeriodic (fun y => g y • a y) := by
    intro x n
    change g (x + fun j => (n j : ℝ)) • a (x + fun j => (n j : ℝ)) = g x • a x
    rw [hpg x n, hpa x n]
  have hi := divergence_periodic_integral_zero (hg.smul ha) hp
  have he (x : Plane) : PlanarHamiltonian.divergence (g • a) x =
      fderiv ℝ g x (a x) := by
    rw [show g • a = (fun y => g y • a y) from rfl,
      divergence_scalar_product ha hg, hdiv, mul_zero, zero_add]
  simpa only [he] using hi

theorem scalarGenerator_integral_zero {a : Plane → Plane} {g : Plane → ℝ}
    (ha : ContDiff ℝ ∞ a) (hg : ContDiff ℝ ∞ g)
    (hpa : PlanePeriodic a) (hpg : PlanePeriodic g)
    (hdiv : ∀ x, PlanarHamiltonian.divergence a x = 0) (ν : ℝ) :
    (∫ x in Icc (0 : Plane) (fun _ => 1), scalarGenerator ν a g x) = 0 := by
  have hL : Continuous (scalarLaplacian g) := by
    apply continuous_finsetSum
    intro j _
    exact (spatialD_smooth j (spatialD_smooth j hg)).continuous
  have hD : Continuous (fun x => fderiv ℝ g x (a x)) :=
    ((hg.fderiv_right (m := ∞) (by simp)).clm_apply ha).continuous
  simp_rw [scalarGenerator]
  rw [integral_sub (hL.const_mul ν).integrableOn_Icc hD.integrableOn_Icc,
    integral_const_mul, scalarLaplacian_integral_zero hg hpg,
    scalar_transport_integral_zero ha hg hpa hpg hdiv]
  simp

end ForcedComputation.VelocityDetector

end

end OAI
