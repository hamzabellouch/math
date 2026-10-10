import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSlowAsymptotic
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralExpansionUniqueness

namespace OAI

/-! The actual free outgoing correction equals the explicit angular H column. -/

open Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralFreeFirstColumn (ell : ℕ) (q : ℂ) (t : ℝ) : E₄ :=
  (spectralFreeSlowJet q (ell+6) t,0)

theorem spectralFreeFirstColumn_hasDerivAt (ell : ℕ) (q νm : ℂ)
    (hq : -1 < q.re) (t : ℝ) :
    HasDerivAt (spectralFreeFirstColumn ell q)
      (circularLeadingField t (spectralFreeFirstColumn ell q t)+
        circularBoundedField ((ell : ℂ)-2*q) νm ((ell*(ell+10) : ℕ) : ℂ)
          1 0 (spectralFreeFirstColumn ell q t)) t := by
  have h := (spectralFreeAngularJet_hasDerivAt ell q hq t).prodMk
    (hasDerivAt_const t (0 : ℂ × ℂ))
  apply h.congr_deriv
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [spectralFreeFirstColumn,circularLeadingField,circularBoundedField,
      spectralDiagonalCoefficient,spectralCrossCoefficient,Prod.fst_add,Prod.snd_add,
      Prod.fst_zero,Prod.snd_zero,zero_pow (by omega : 1 ≠ 0),zero_pow (by omega : 1+1 ≠ 0),
      mul_zero,zero_mul,star_zero,add_zero,zero_add,sub_zero]
  ring

theorem spectralFreeFirstColumn_remainder (ell : ℕ) (q νm : ℂ)
    (hq : -1 < q.re) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, Real.log 4/2 ≤ t →
      ‖spectralFreeFirstColumn ell q t-circularPolynomialJet
        (spectralOutgoingPolynomial ((ell : ℂ)-2*q) νm ((ell*(ell+10) : ℕ) : ℂ)
          1 0 (1,0) (j+1)) t‖ ≤ C*Real.exp (-(2*((j+2 : ℕ) : ℝ))*t) := by
  obtain ⟨C,hC,hb⟩ := spectralFreeSlowJet_remainder ell q hq j
  refine ⟨C,hC,?_⟩
  intro t ht
  rw [spectralOutgoingPolynomial_free_first]
  simpa [spectralFreeFirstColumn,circularPolynomialJet,radialPolynomialJet,
    radialExteriorPolynomialFunction,radialPolynomialEuler,Prod.norm_def] using hb t ht

theorem spectralFreeFirstColumn_eq_correction (ell : ℕ) (q νm : ℂ)
    (hq : -1 < q.re) (j : ℕ) (w : CircularTailSpace) (T : ℝ)
    (hgap : circularFieldBound ((ell : ℂ)-2*q) νm ((ell*(ell+10) : ℕ) : ℂ)
      1 0 < 2*((j+1 : ℕ) : ℝ))
    (hY : ∀ t, T ≤ t → HasDerivAt
      (fun s => circularPolynomialJet
        (spectralOutgoingPolynomial ((ell : ℂ)-2*q) νm ((ell*(ell+10) : ℕ) : ℂ)
          1 0 (1,0) (j+1)) s+circularUnweight (2*((j+1 : ℕ) : ℝ)) w s)
      (circularLeadingField t (circularPolynomialJet
        (spectralOutgoingPolynomial ((ell : ℂ)-2*q) νm ((ell*(ell+10) : ℕ) : ℂ)
          1 0 (1,0) (j+1)) t+circularUnweight (2*((j+1 : ℕ) : ℝ)) w t)+
       circularBoundedField ((ell : ℂ)-2*q) νm ((ell*(ell+10) : ℕ) : ℂ) 1 0
        (circularPolynomialJet
          (spectralOutgoingPolynomial ((ell : ℂ)-2*q) νm ((ell*(ell+10) : ℕ) : ℂ)
            1 0 (1,0) (j+1)) t+circularUnweight (2*((j+1 : ℕ) : ℝ)) w t)) t) :
    ∀ t, max T (max 0 (Real.log 4/2)) ≤ t →
      circularPolynomialJet
        (spectralOutgoingPolynomial ((ell : ℂ)-2*q) νm ((ell*(ell+10) : ℕ) : ℂ)
          1 0 (1,0) (j+1)) t+circularUnweight (2*((j+1 : ℕ) : ℝ)) w t=
        spectralFreeFirstColumn ell q t := by
  let P := spectralOutgoingPolynomial ((ell : ℂ)-2*q) νm ((ell*(ell+10) : ℕ) : ℂ)
    1 0 (1,0) (j+1)
  let Y := fun s => circularPolynomialJet P s+circularUnweight (2*((j+1 : ℕ) : ℝ)) w s
  let S := max T (max 0 (Real.log 4/2))
  obtain ⟨C,hC,hb⟩ := spectralFreeFirstColumn_remainder ell q νm hq j
  intro t ht
  apply circular_fast_decay_unique ((ell : ℂ)-2*q) νm ((ell*(ell+10) : ℕ) : ℂ)
    1 (by omega) 0 (2*((j+1 : ℕ) : ℝ)) (C+‖w‖) S (fun _ => 0) Y
    (spectralFreeFirstColumn ell q) (by simp) (fun s hs => hY s ((le_max_left _ _).trans hs))
    (fun s _ => spectralFreeFirstColumn_hasDerivAt ell q νm hq s) _ hgap t ht
  intro s hs
  have hs0 : 0 ≤ s := (le_max_left 0 _).trans ((le_max_right T _).trans hs)
  have hsl : Real.log 4/2 ≤ s := (le_max_right 0 _).trans ((le_max_right T _).trans hs)
  have he : Real.exp (-(2*((j+2 : ℕ) : ℝ))*s) ≤
      Real.exp (-(2*((j+1 : ℕ) : ℝ))*s) := by
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  change ‖(circularPolynomialJet P s+circularUnweight (2*((j+1 : ℕ) : ℝ)) w s)-
    spectralFreeFirstColumn ell q s‖ ≤ _
  calc
    _ ≤ ‖circularPolynomialJet P s-spectralFreeFirstColumn ell q s‖+
        ‖circularUnweight (2*((j+1 : ℕ) : ℝ)) w s‖ := by
      rw [show circularPolynomialJet P s+circularUnweight (2*((j+1 : ℕ) : ℝ)) w s-
        spectralFreeFirstColumn ell q s=(circularPolynomialJet P s-
          spectralFreeFirstColumn ell q s)+circularUnweight (2*((j+1 : ℕ) : ℝ)) w s by abel]
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
