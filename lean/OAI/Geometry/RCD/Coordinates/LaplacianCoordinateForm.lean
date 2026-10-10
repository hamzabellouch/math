import OAI.Geometry.RCD.Coordinates.RegularSquareLaplacian
import OAI.Geometry.RCD.Coordinates.CoordinateBilinear

namespace OAI

/-! # Pointwise linear representatives of the actual finite Laplacian map -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) {m : ℕ}

/-- Evaluation of the finitely many L² source coordinates defines a
pointwise linear form without choosing representatives for each direction. -/
def laplacianCoordinateForm (D : Euclidean m →L[ℝ] Lp ℝ 2 μ) (x : X) :
    Euclidean m →ₗ[ℝ] ℝ :=
  (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.constr ℝ
    (fun i => D (EuclideanSpace.single i 1) x)

theorem laplacianCoordinateForm_apply (D : Euclidean m →L[ℝ] Lp ℝ 2 μ)
    (x : X) (a : Euclidean m) :
    laplacianCoordinateForm μ D x a=∑ i, a i*D (EuclideanSpace.single i 1) x := by
  simp only [laplacianCoordinateForm,Module.Basis.constr_apply_fintype,smul_eq_mul]
  rfl

theorem laplacianCoordinateForm_rep (D : Euclidean m →L[ℝ] Lp ℝ 2 μ) (a : Euclidean m) :
    D a =ᵐ[μ] fun x => laplacianCoordinateForm μ D x a := by
  let b := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  have he : b.constr ℝ (fun i => D (EuclideanSpace.single i 1))=D.toLinearMap := by
    apply b.ext
    intro i
    simp [b,EuclideanSpace.basisFun_apply]
  have hs : D a=∑ i, a i • D (EuclideanSpace.single i 1) := by
    have h := congrArg (fun F : Euclidean m →ₗ[ℝ] Lp ℝ 2 μ => F a) he
    rw [Module.Basis.constr_apply_fintype] at h
    exact h.symm
  rw [hs]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i : Fin m => a i • D (EuclideanSpace.single i 1)),
    ae_all_iff.mpr (fun i : Fin m => Lp.coeFn_smul (a i) (D (EuclideanSpace.single i 1)))]
    with x hx hy
  rw [laplacianCoordinateForm_apply, hx]
  exact Finset.sum_congr rfl (fun i _ => hy i)

variable [MetricSpace X] [BorelSpace X] [ProperSpace X]
  (hQ : QuadraticCheegerEnergy μ) [μ.Regular]

/-- The source of an actual squared direction is the exact linear source
correction used by the shifted quadratic-perturbation argument. -/
theorem laplacianCoordinateForm_square
    (U : Euclidean m →L[ℝ] SobolevSpace μ hQ) (D : Euclidean m →L[ℝ] Lp ℝ 2 μ)
    (hD : ∀ a, IsWeakLaplacian μ hQ (U a) (D a))
    (w z : Euclidean m) (A L : ℝ≥0)
    (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (U w) x|≤A)
    (hL : ∀ᵐ x ∂μ, localGamma μ hQ (U w) (U w) x≤(L:ℝ)^2)
    (hz : U z=SobolevSpace.product μ hQ (U w) (U w) A A) :
    ∀ᵐ x ∂μ, laplacianCoordinateForm μ D x z =
      2*SobolevSpace.toLp μ hQ (U w) x*laplacianCoordinateForm μ D x w+
        2*localGamma μ hQ (U w) (U w) x := by
  obtain ⟨q,hq,hqr⟩ := (hD w).product μ hQ (U w) (U w) (D w) (D w)
    (hD w) A A L hA hA hL
  have hqz : D z=q := IsWeakLaplacian.unique μ hQ (by simpa only [hz] using hD z) hq
  filter_upwards [hqr,laplacianCoordinateForm_rep μ D z,laplacianCoordinateForm_rep μ D w]
    with x hq hz hw
  rw [← hz,hqz,hq,hw]
  ring

end RegularPointCoordinates

end

end OAI
