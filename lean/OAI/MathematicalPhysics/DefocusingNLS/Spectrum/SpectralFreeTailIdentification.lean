import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSlowIdentification
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSecondIdentification

namespace OAI

/-! Identify a zero-profile outgoing expansion without unfolding its construction. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralFreeFirst_eq_of_tail (ell : ℕ) (q ν : ℂ)
    (hq : -1 < q.re) (j : ℕ) (Y : ℝ → E₄) (v : CircularTailSpace)
    (hgap : circularFieldBound ((ell : ℂ)-2*q) ν ((ell*(ell+10) : ℕ) : ℂ) 1 0 < 2*((j+1 : ℕ) : ℝ))
    (hYd : ∀ t, 0 ≤ t → HasDerivAt Y (circularLeadingField t (Y t) +
      circularBoundedField ((ell : ℂ)-2*q) ν ((ell*(ell+10) : ℕ) : ℂ) 1 0 (Y t)) t)
    (hYe : ∀ t, Y t = circularPolynomialJet
      (spectralOutgoingPolynomial ((ell : ℂ)-2*q) ν ((ell*(ell+10) : ℕ) : ℂ) 1 0 (1,0) (j+1)) t +
        circularUnweight (2*((j+1 : ℕ) : ℝ)) v t) :
    ∀ t, max 0 (Real.log 4/2) ≤ t → Y t = spectralFreeFirstColumn ell q t := by
  have hf : Y = (fun t => circularPolynomialJet
      (spectralOutgoingPolynomial ((ell : ℂ)-2*q) ν ((ell*(ell+10) : ℕ) : ℂ) 1 0 (1,0) (j+1)) t +
      circularUnweight (2*((j+1 : ℕ) : ℝ)) v t) := funext hYe
  subst Y
  have hi := spectralFreeFirstColumn_eq_correction ell q ν hq j v 0 hgap hYd
  intro t ht
  exact hi t ((max_le (le_max_left 0 _) le_rfl).trans ht)

theorem spectralFreeSecond_eq_of_tail (ell : ℕ) (q ν : ℂ)
    (hq : -1 < q.re) (j : ℕ) (Y : ℝ → E₄) (v : CircularTailSpace)
    (hgap : circularFieldBound ν ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ) 1 0 < 2*((j+1 : ℕ) : ℝ))
    (hYd : ∀ t, 0 ≤ t → HasDerivAt Y (circularLeadingField t (Y t) +
      circularBoundedField ν ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ) 1 0 (Y t)) t)
    (hYe : ∀ t, Y t = circularPolynomialJet
      (spectralOutgoingPolynomial ν ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ) 1 0 (0,1) (j+1)) t +
        circularUnweight (2*((j+1 : ℕ) : ℝ)) v t) :
    ∀ t, max 0 (Real.log 4/2) ≤ t → Y t = spectralFreeSecondColumn ell q t := by
  have hf : Y = (fun t => circularPolynomialJet
      (spectralOutgoingPolynomial ν ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ) 1 0 (0,1) (j+1)) t +
      circularUnweight (2*((j+1 : ℕ) : ℝ)) v t) := funext hYe
  subst Y
  have hi := spectralFreeSecondColumn_eq_correction ell q ν hq j v 0 hgap hYd
  intro t ht
  exact hi t ((max_le (le_max_left 0 _) le_rfl).trans ht)

end DefocusingNLS

end OAI
