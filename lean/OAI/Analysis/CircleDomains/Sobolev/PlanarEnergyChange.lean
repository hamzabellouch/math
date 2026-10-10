import OAI.Analysis.CircleDomains.Sobolev.EnergyChangeCoordinates
import Mathlib.MeasureTheory.Function.Jacobian

namespace OAI

/-!
# The integral energy formula in the real chart

Mathlib's change-of-variables theorem combines with the proved
covector pullback identity. This works on arbitrary measurable subsets,
including each mask and each localized tail of a finite completion.
-/

open Set Matrix MeasureTheory

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def planeDerivativeMatrix (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) : PlanarMetric :=
  LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) A.toLinearMap

theorem det_planeDerivativeMatrix (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
    (planeDerivativeMatrix A).det = A.det :=
  LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ) A.toLinearMap

/-- Dirichlet energy of a target covector field equals energy of its
actual pullback in any conformally rescaled pullback metric. -/
theorem integral_covectorEnergy_change_variables
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (f : (ℝ × ℝ) → (ℝ × ℝ)) (A : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (A x) s x) (hinj : InjOn f s)
    (hdet : ∀ x ∈ s, (A x).det ≠ 0)
    (v : (ℝ × ℝ) → Fin 2 → ℝ) (g : (ℝ × ℝ) → PlanarMetric)
    (hPD : ∀ x ∈ s, (g (f x)).PosDef)
    (c : (ℝ × ℝ) → ℝ) (hc : ∀ x ∈ s, 0 < c x) :
    (∫ y in f '' s, covectorEnergy (v y) (g y)) =
      ∫ x in s, covectorEnergy ((planeDerivativeMatrix (A x))ᵀ *ᵥ v (f x))
        (c x • ((planeDerivativeMatrix (A x))ᵀ * g (f x) * planeDerivativeMatrix (A x))) := by
  refine (integral_image_eq_integral_abs_det_fderiv_smul volume hs hf hinj
    (fun y => covectorEnergy (v y) (g y))).trans ?_
  apply setIntegral_congr_fun hs
  intro x hx
  simp only [smul_eq_mul]
  have hB : (planeDerivativeMatrix (A x)).det ≠ 0 := by
    simpa only [det_planeDerivativeMatrix] using hdet x hx
  simpa only [det_planeDerivativeMatrix] using
    (covectorEnergy_conformal_pullback (v (f x)) (hPD x hx) hB (hc x hx)).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
