import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.PointFourierPolynomial
import OAI.Analysis.RieszRectifiability.Kernel.CommonHeightLocalIntegrability

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Function
open scoped NNReal

theorem common_height_ae_polynomial {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π)
    (hleft : LeftInverse π e) (a : Ambient d) (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d)
    (hplane : e = affinePlaneSection a L) (f : Ambient d → ℝ)
    (hf : ∀ H, MemLp f 2
      ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))
    (T : 𝓢'(Ambient (p + 1), ℂ))
    (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, f (a + L x) • g x)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, f (a + L x) • fractionalSchwartzTest p g x) = 0) :
    ∃ P : MvPolynomial (Fin (p + 1)) ℂ,
      ∀ᵐ x, (f (a + L x) : ℂ) = MvPolynomial.eval (fun j => (x j : ℂ)) P := by
  exact represented_fractional_height_ae_polynomial p (fun x => f (a + L x))
    (common_height_intrinsic_locallyIntegrable e π K Q he hπ hleft a L hplane f hf)
    T hT heq

theorem polynomial_inherits_height_tail {d : ℕ} (q : ℕ)
    (w : Ambient d → ℝ) (P : MvPolynomial (Fin d) ℂ)
    (hP : ∀ᵐ x, (w x : ℂ) = MvPolynomial.eval (fun j => (x j : ℂ)) P)
    (R : ℝ)
    (hi : IntegrableOn (fun x => |w x| * inverseDistancePow q 0 x)
      (closedExterior 0 R)) :
    IntegrableOn (fun x => ‖MvPolynomial.eval (fun j => (x j : ℂ)) P‖ *
      inverseDistancePow q 0 x) (closedExterior 0 R) := by
  apply hi.congr
  filter_upwards [ae_restrict_of_ae hP] with x hx
  rw [← hx, Complex.norm_real, Real.norm_eq_abs]

end

end RieszRectifiability

end OAI
