import OAI.Geometry.RCD.Coordinates.GammaCoordinateForm
import OAI.Geometry.RCD.Sobolev.HessianActionLocality

namespace OAI

/-! # Finite bilinear representatives of the actual Hessian action -/

open Set Filter MeasureTheory
open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) {m : ℕ}

theorem gamma_bilinear_right_rep (f : SobolevSpace μ hQ)
    (B : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ) (a b : Euclidean m) :
    localGamma μ hQ f (B a b) =ᵐ[μ] fun x =>
      coordinateBilinear (fun i j => localGamma μ hQ f
        (B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) x) a b := by
  classical
  let e (i : Fin m) : Euclidean m := EuclideanSpace.single i 1
  have he : coordinateBilinear (fun i j => B (e i) (e j))=B := by
    apply (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ext
    intro i
    apply (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ext
    intro j
    simp [coordinateBilinear,EuclideanSpace.basisFun_apply,e]
  have hb : B a b=∑ i : Fin m, ∑ j : Fin m, (a i*b j) • B (e i) (e j) := by
    have hh := congrArg (fun T : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ => T a b) he
    rw [coordinateBilinear_apply] at hh
    exact hh.symm
  have hout := localGamma_finset_sum_right μ hQ Finset.univ f
    (fun i => ∑ j : Fin m, (a i*b j) • B (e i) (e j))
  have hin (i : Fin m) := localGamma_finset_sum_right μ hQ Finset.univ f
    (fun j => (a i*b j) • B (e i) (e j))
  have hs (i j : Fin m) := localGamma_smul_right μ hQ (a i*b j) f (B (e i) (e j))
  rw [hb]
  filter_upwards [hout,ae_all_iff.mpr hin,ae_all_iff.mpr (fun i => ae_all_iff.mpr (hs i))]
    with x ho hi hs
  rw [ho]
  simp only [coordinateBilinear_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hi i]
  exact Finset.sum_congr rfl (fun j _ => hs i j)

def hessianCoordinateForm (f : SobolevSpace μ hQ)
    (U G : Euclidean m →L[ℝ] SobolevSpace μ hQ)
    (B : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ) (x : X) :
    Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ :=
  (1/2:ℝ) • (gammaCoordinateForm μ hQ U G x+(gammaCoordinateForm μ hQ U G x).flip-
    coordinateBilinear (fun i j => localGamma μ hQ f
      (B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) x))

/-- Finite bilinear representatives preserve the full three-term action. -/
theorem hessianCoordinateForm_rep (f : SobolevSpace μ hQ)
    (U G : Euclidean m →L[ℝ] SobolevSpace μ hQ)
    (B : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ) (a b : Euclidean m) :
    localHessianAction μ hQ f (U a) (U b) (G a) (G b) (B a b) =ᵐ[μ]
      fun x => hessianCoordinateForm μ hQ f U G B x a b := by
  filter_upwards [gammaCoordinateForm_rep μ hQ U G a b,gammaCoordinateForm_rep μ hQ U G b a,
    gamma_bilinear_right_rep μ hQ f B a b] with x h₁ h₂ h₃
  change (localGamma μ hQ (U a) (G b) x+localGamma μ hQ (U b) (G a) x-
    localGamma μ hQ f (B a b) x)/2 = (1/2:ℝ)*_
  rw [h₁,h₂,h₃]
  simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.flip_apply]
  ring

omit [ProperSpace X] in
theorem hessianCoordinateForm_symmetric (f : SobolevSpace μ hQ)
    (U G : Euclidean m →L[ℝ] SobolevSpace μ hQ)
    (B : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ)
    (hB : ∀ a b, B a b=B b a) (x : X) (a b : Euclidean m) :
    hessianCoordinateForm μ hQ f U G B x a b=hessianCoordinateForm μ hQ f U G B x b a := by
  have hc := coordinateBilinear_symmetric
    (fun i j => localGamma μ hQ f (B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) x)
    (fun i j => by rw [hB]) a b
  change (1/2:ℝ)*(gammaCoordinateForm μ hQ U G x a b+gammaCoordinateForm μ hQ U G x b a-_) =
    (1/2:ℝ)*(gammaCoordinateForm μ hQ U G x b a+gammaCoordinateForm μ hQ U G x a b-_)
  rw [hc]
  ring

end RegularPointCoordinates

end

end OAI
