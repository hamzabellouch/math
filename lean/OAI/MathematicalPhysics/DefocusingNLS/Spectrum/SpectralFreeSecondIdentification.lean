import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSecondColumn

namespace OAI

/-! Identification of the opposite free outgoing correction with its H column. -/

open Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralFreeSecondColumn_eq_correction (ell : ℕ) (q νp : ℂ)
    (hq : -1 < q.re) (j : ℕ) (w : CircularTailSpace) (T : ℝ)
    (hgap : circularFieldBound νp ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ)
      1 0 < 2*((j+1 : ℕ) : ℝ))
    (hY : ∀ t, T ≤ t → HasDerivAt
      (fun s => circularPolynomialJet
        (spectralOutgoingPolynomial νp ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ)
          1 0 (0,1) (j+1)) s+circularUnweight (2*((j+1 : ℕ) : ℝ)) w s)
      (circularLeadingField t (circularPolynomialJet
        (spectralOutgoingPolynomial νp ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ)
          1 0 (0,1) (j+1)) t+circularUnweight (2*((j+1 : ℕ) : ℝ)) w t)+
       circularBoundedField νp ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ) 1 0
        (circularPolynomialJet
          (spectralOutgoingPolynomial νp ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ)
            1 0 (0,1) (j+1)) t+circularUnweight (2*((j+1 : ℕ) : ℝ)) w t)) t) :
    ∀ t, max T (max 0 (Real.log 4/2)) ≤ t →
      circularPolynomialJet
        (spectralOutgoingPolynomial νp ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ)
          1 0 (0,1) (j+1)) t+circularUnweight (2*((j+1 : ℕ) : ℝ)) w t=
        spectralFreeSecondColumn ell q t := by
  let P := spectralOutgoingPolynomial νp ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ)
    1 0 (0,1) (j+1)
  let Y := fun s => circularPolynomialJet P s+circularUnweight (2*((j+1 : ℕ) : ℝ)) w s
  let S := max T (max 0 (Real.log 4/2))
  obtain ⟨C,hC,hb⟩ := spectralFreeSecondColumn_remainder ell q νp hq j
  intro t ht
  apply circular_fast_decay_unique νp ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ)
    1 (by omega) 0 (2*((j+1 : ℕ) : ℝ)) (C+‖w‖) S (fun _ => 0) Y
    (spectralFreeSecondColumn ell q) (by simp) (fun s hs => hY s ((le_max_left _ _).trans hs))
    (fun s _ => spectralFreeSecondColumn_hasDerivAt ell q νp hq s) _ hgap t ht
  intro s hs
  have hs0 : 0 ≤ s := (le_max_left 0 _).trans ((le_max_right T _).trans hs)
  have hsl : Real.log 4/2 ≤ s := (le_max_right 0 _).trans ((le_max_right T _).trans hs)
  have he : Real.exp (-(2*((j+2 : ℕ) : ℝ))*s) ≤
      Real.exp (-(2*((j+1 : ℕ) : ℝ))*s) := by
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  change ‖(circularPolynomialJet P s+circularUnweight (2*((j+1 : ℕ) : ℝ)) w s)-
    spectralFreeSecondColumn ell q s‖ ≤ _
  calc
    _ ≤ ‖circularPolynomialJet P s-spectralFreeSecondColumn ell q s‖+
        ‖circularUnweight (2*((j+1 : ℕ) : ℝ)) w s‖ := by
      rw [show circularPolynomialJet P s+circularUnweight (2*((j+1 : ℕ) : ℝ)) w s-
        spectralFreeSecondColumn ell q s=(circularPolynomialJet P s-
          spectralFreeSecondColumn ell q s)+circularUnweight (2*((j+1 : ℕ) : ℝ)) w s by abel]
      exact norm_add_le _ _
    _ ≤ C*Real.exp (-(2*((j+2 : ℕ) : ℝ))*s)+
        Real.exp (-(2*((j+1 : ℕ) : ℝ))*s)*‖w‖ :=
      add_le_add (by simpa only [norm_sub_rev] using hb s hsl) (circularUnweight_norm _ _ _)
    _ ≤ C*Real.exp (-(2*((j+1 : ℕ) : ℝ))*s)+
        Real.exp (-(2*((j+1 : ℕ) : ℝ))*s)*‖w‖ :=
      add_le_add (mul_le_mul_of_nonneg_left he hC) le_rfl
    _ = _ := by ring


end DefocusingNLS

end OAI
