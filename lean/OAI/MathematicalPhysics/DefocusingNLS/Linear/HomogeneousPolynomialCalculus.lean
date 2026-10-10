import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPolynomialLaplacian
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicTestCalculus

namespace OAI

/-! # Cartesian realization of the algebraic polynomial Laplacian

This identifies the algebraic harmonic polynomials used in the sphere-density
argument with smooth Cartesian harmonic functions.
-/

open MvPolynomial
open scoped ContDiff Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def physicalPolynomialFunction : PhysicalRealPolynomial →ₐ[ℝ] (E → ℂ) :=
  MvPolynomial.aeval (fun i x => (x i : ℂ))

@[simp] theorem physicalPolynomialFunction_C (c : ℝ) (x : E) :
    physicalPolynomialFunction (C c) x = (c : ℂ) := by
  simp [physicalPolynomialFunction]

@[simp] theorem physicalPolynomialFunction_X (i : Fin 12) (x : E) :
    physicalPolynomialFunction (X i) x = (x i : ℂ) := by
  simp [physicalPolynomialFunction]

@[simp] theorem physicalPolynomialFunction_C_eq (c : ℝ) :
    physicalPolynomialFunction (C c) = (fun _ : E => (c : ℂ)) := by
  funext x
  exact physicalPolynomialFunction_C c x

@[simp] theorem physicalPolynomialFunction_X_eq (i : Fin 12) :
    physicalPolynomialFunction (X i) = (fun x : E => (x i : ℂ)) := by
  funext x
  exact physicalPolynomialFunction_X i x

theorem physicalPolynomialFunction_eval (p : PhysicalRealPolynomial) (x : E) :
    physicalPolynomialFunction p x = (MvPolynomial.eval (fun i => x i) p : ℂ) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, Pi.add_apply, hp, hq, Complex.ofReal_add]
  | mul_X p i hp =>
    simp only [map_mul, Pi.mul_apply, physicalPolynomialFunction_X, MvPolynomial.eval_X,
      Complex.ofReal_mul, hp]

theorem physicalPolynomialFunction_contDiff (p : PhysicalRealPolynomial) :
    ContDiff ℝ ∞ (physicalPolynomialFunction p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [physicalPolynomialFunction_C_eq] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (c : ℂ)))
  | add p q hp hq =>
    have he : physicalPolynomialFunction (p + q) =
        (fun x => physicalPolynomialFunction p x + physicalPolynomialFunction q x) := by
      funext x
      simp only [map_add, Pi.add_apply]
    rw [he]
    exact hp.add hq
  | mul_X p i hp =>
    have hi : ContDiff ℝ ∞ (fun x : E => (x i : ℂ)) := by
      simpa only [Function.comp_def, PiLp.proj_apply, Complex.ofRealCLM_apply] using
        Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
    have he : physicalPolynomialFunction (p * X i) =
        (fun x => physicalPolynomialFunction p x * (x i : ℂ)) := by
      funext x
      simp only [map_mul, Pi.mul_apply, physicalPolynomialFunction_X]
    rw [he]
    exact hp.mul hi

theorem physicalPolynomialFunction_fderiv_basis (p : PhysicalRealPolynomial)
    (x : E) (i : Fin 12) :
    fderiv ℝ (physicalPolynomialFunction p) x (EuclideanSpace.basisFun (Fin 12) ℝ i) =
      physicalPolynomialFunction (pderiv i p) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [physicalPolynomialFunction_C_eq, pderiv_C]
    simp
  | add p q hp hq =>
    rw [map_add, fderiv_add ((physicalPolynomialFunction_contDiff p).differentiable
      (by simp) x) ((physicalPolynomialFunction_contDiff q).differentiable (by simp) x)]
    simpa only [add_apply, map_add, Pi.add_apply] using congrArg₂ (· + ·) hp hq
  | mul_X p j hp =>
    have hj : DifferentiableAt ℝ (physicalPolynomialFunction (X j)) x :=
      (physicalPolynomialFunction_contDiff (X j)).differentiable (by simp) x
    have hx : fderiv ℝ (physicalPolynomialFunction (X j)) x =
        Complex.ofRealCLM.comp (EuclideanSpace.proj j) := by
      simpa only [physicalPolynomialFunction_X_eq, Function.comp_def, PiLp.proj_apply,
        Complex.ofRealCLM_apply] using
        (Complex.ofRealCLM.hasFDerivAt.comp x (EuclideanSpace.proj j).hasFDerivAt).fderiv
    rw [map_mul, fderiv_mul ((physicalPolynomialFunction_contDiff p).differentiable
      (by simp) x) hj]
    simp only [add_apply, smul_apply, smul_eq_mul,
      hx, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, PiLp.proj_apply,
      EuclideanSpace.basisFun_apply, PiLp.single_apply, pderiv_mul, pderiv_X,
      Pi.single_apply, map_add, map_mul, Pi.add_apply, Pi.mul_apply,
      physicalPolynomialFunction_X]
    split_ifs <;> simp_all <;> ring

theorem physicalPolynomialFunction_laplacian (p : PhysicalRealPolynomial) (x : E) :
    Δ (physicalPolynomialFunction p) x =
      physicalPolynomialFunction (physicalPolynomialLaplacian p) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 12) ℝ), physicalPolynomialLaplacian_apply, map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [radial_second_directional_eq _ x _
    ((physicalPolynomialFunction_contDiff p).of_le (by simp)).contDiffAt]
  simp only [physicalPolynomialFunction_fderiv_basis]

theorem physicalPolynomialFunction_euler (p : PhysicalRealPolynomial)
    (n : ℕ) (hp : p.IsHomogeneous n) (x : E) :
    fderiv ℝ (physicalPolynomialFunction p) x x =
      (n : ℂ) * physicalPolynomialFunction p x := by
  rw [← radial_basis_derivative_contraction]
  simp_rw [EuclideanSpace.inner_basisFun_real, physicalPolynomialFunction_fderiv_basis]
  have h := congrArg (fun q : PhysicalRealPolynomial => physicalPolynomialFunction q x)
    hp.sum_X_mul_pderiv
  simpa [nsmul_eq_mul] using h

theorem physicalPolynomialFunction_smul (p : PhysicalRealPolynomial)
    (n : ℕ) (hp : p.IsHomogeneous n) (t : ℝ) (x : E) :
    physicalPolynomialFunction p (t • x) =
      (t : ℂ) ^ n * physicalPolynomialFunction p x := by
  rw [physicalPolynomialFunction_eval, physicalPolynomialFunction_eval, p.as_sum]
  simp only [map_sum, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  simp only [PiLp.smul_apply, smul_eq_mul, mul_pow, Finsupp.prod, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← hp.degree_eq_sum_deg_support hd,
    Complex.ofReal_mul, Complex.ofReal_pow]
  ring

end DefocusingNLS

end OAI
