import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.PolynomialTailDegreeOne
import OAI.Analysis.RieszRectifiability.Flatness.DegreeOnePolynomialAffine
import OAI.Analysis.RieszRectifiability.Kernel.CommonHeightPolynomial

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Function
open scoped NNReal

theorem represented_fractional_height_ae_affine (p : ℕ)
    (w : Ambient (p + 1) → ℝ) (hw : LocallyIntegrable w)
    (T : 𝓢'(Ambient (p + 1), ℂ))
    (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, w x • g x)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, w x • fractionalSchwartzTest p g x) = 0)
    (htail : IntegrableOn (fun x => |w x| * inverseDistancePow (p + 1 + 2) 0 x)
      (closedExterior 0 1)) :
    ∃ c : ℝ, ∃ L : Ambient (p + 1) →L[ℝ] ℝ, ∀ᵐ x, w x = c + L x := by
  obtain ⟨P, hP⟩ := represented_fractional_height_ae_polynomial p w hw T hT heq
  have hPi := polynomial_inherits_height_tail (p + 1 + 2) w P hP 1 htail
  obtain ⟨Q, hQ, hPQ⟩ := polynomial_tail_has_degree_one_representative P hPi
  obtain ⟨c, L, hL⟩ := degree_one_polynomial_eval_affine Q hQ
  refine ⟨c.re, Complex.reCLM.comp L, ?_⟩
  filter_upwards [hP] with x hx
  have hv : (w x : ℂ) = c + L x := hx.trans ((hPQ x).trans (hL x))
  change w x = c.re + (L x).re
  simpa only [Complex.ofReal_re, Complex.add_re] using! congrArg Complex.re hv

theorem common_height_intrinsic_ae_affine {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π)
    (hleft : LeftInverse π e) (a : Ambient d) (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d)
    (hplane : e = affinePlaneSection a L) (f : Ambient d → ℝ)
    (hf : ∀ H, MemLp f 2
      ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))
    (T : 𝓢'(Ambient (p + 1), ℂ))
    (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, f (a + L x) • g x)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, f (a + L x) • fractionalSchwartzTest p g x) = 0)
    (htail : IntegrableOn (fun x => |f x| * inverseDistancePow (p + 1 + 2) (e 0) x)
      (closedExterior (e 0) 1) (coordinatePlaneMeasure e)) :
    ∃ c : ℝ, ∃ M : Ambient (p + 1) →L[ℝ] ℝ, ∀ᵐ x, f (a + L x) = c + M x := by
  have he0 : e 0 = a := by rw [hplane]; simp [affinePlaneSection]
  have htail' := htail
  rw [he0, hplane] at htail'
  exact represented_fractional_height_ae_affine p (fun x => f (a + L x))
    (common_height_intrinsic_locallyIntegrable e π K Q he hπ hleft a L hplane f hf)
    T hT heq (height_tail_integrable_affine_pullback (p + 1 + 2) a L f 1 htail')

end

end RieszRectifiability

end OAI
