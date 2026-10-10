import Mathlib
import OAI.Analysis.AffineBernstein.Basic

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- The augmented tangent frame, with its transverse column last. -/
def parametricFrame {n : ℕ} (X : Space n → E) (ξ : E) (x : Space n) :
    Fin n ⊕ Unit → E :=
  Sum.elim (fun i => fderiv ℝ X x (coordinateVector n i)) (fun _ => ξ)

/- The literal second form with a conormal frozen at the point in question. -/
def parametricSecondForm {n : ℕ} (X : Space n → E) (ν : E →L[ℝ] ℝ)
    (x : Space n) : Matrix (Fin n) (Fin n) ℝ := hessian (fun y => ν (X y)) x

/- Source (affine-area), using a fixed ambient volume basis. -/
def parametricAreaDensity {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    (X : Space n → E) (ν : E →L[ℝ] ℝ) (ξ : E) (x : Space n) : ℝ :=
  Real.rpow (parametricSecondForm X ν x).det (1 / ((n : ℝ) + 2)) *
    Real.rpow |b.det (parametricFrame X ξ x)| ((n : ℝ) / ((n : ℝ) + 2))

lemma hessian_add_constant {n : ℕ} (f : Space n → ℝ) (r : ℝ) (x : Space n) :
    hessian (fun y => f y + r) x = hessian f x := by
  ext i j
  simp only [hessian, fderiv_add_const]

lemma parametricSecondForm_affine {n : ℕ} (X : Space n → E)
    (L : E ≃L[ℝ] E) (v : E) (ν : E →L[ℝ] ℝ) (x : Space n) :
    parametricSecondForm (fun y => L (X y) + v) (ν.comp L.symm.toContinuousLinearMap) x =
      parametricSecondForm X ν x := by
  have he : (fun y => (ν.comp L.symm.toContinuousLinearMap) (L (X y) + v)) =
      (fun y => ν (X y) + ν (L.symm v)) := by
    funext y
    simp
  simp only [parametricSecondForm, he, hessian_add_constant]

lemma parametricFrame_affine {n : ℕ} {X : Space n → E} {x : Space n}
    (hX : DifferentiableAt ℝ X x) (L : E ≃L[ℝ] E) (v ξ : E) :
    parametricFrame (fun y => L (X y) + v) (L ξ) x =
      L.toLinearEquiv.toLinearMap ∘ parametricFrame X ξ x := by
  have hd := ((L.hasFDerivAt.comp x hX.hasFDerivAt).add_const v).fderiv
  funext i
  rcases i with i | i
  · change (fderiv ℝ (fun y => L (X y) + v) x) (coordinateVector n i) = _
    convert! congrArg (fun T : Space n →L[ℝ] E => T (coordinateVector n i)) hd using 1
  · rfl

/- Full ambient affine covariance, not restricted to fiber-preserving maps. -/
theorem parametricAreaDensity_affine {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    {X : Space n → E} {x : Space n} (hX : DifferentiableAt ℝ X x)
    (L : E ≃L[ℝ] E) (v ξ : E) (ν : E →L[ℝ] ℝ) :
    parametricAreaDensity b (fun y => L (X y) + v)
      (ν.comp L.symm.toContinuousLinearMap) (L ξ) x =
      Real.rpow |LinearMap.det L.toLinearEquiv.toLinearMap| ((n : ℝ) / ((n : ℝ) + 2)) *
        parametricAreaDensity b X ν ξ x := by
  rw [parametricAreaDensity, parametricSecondForm_affine,
    parametricFrame_affine hX, b.det_comp, abs_mul]
  have hr := Real.mul_rpow (z := (n : ℝ) / ((n : ℝ) + 2))
    (abs_nonneg (LinearMap.det L.toLinearEquiv.toLinearMap))
    (abs_nonneg (b.det (parametricFrame X ξ x)))
  change Real.rpow _ _ = _ at hr
  rw [hr]
  unfold parametricAreaDensity
  simp only [Real.rpow_eq_pow]
  ring

end AffineBernstein
end

end OAI
