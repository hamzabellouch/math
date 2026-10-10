import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialJet
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularUnweight

namespace OAI

/-! Adding a decaying correction to a polynomial spectral column. -/

open Polynomial
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circularLeadingField_add (t : ℝ) (z w : E₄) :
    circularLeadingField t (z+w)=circularLeadingField t z+circularLeadingField t w := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp [circularLeadingField,mul_add]

theorem circularBoundedField_add (νp νm η : ℂ) (m : ℕ) (q : ℂ) (z w : E₄) :
    circularBoundedField νp νm η m q (z+w)=
      circularBoundedField νp νm η m q z+circularBoundedField νp νm η m q w := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [circularBoundedField,Prod.fst_add,Prod.snd_add]
  all_goals ring

theorem circularPolynomial_corrected (νp νm η : ℂ) (m : ℕ) (P : ℂ[X])
    (U : ℂ[X] × ℂ[X]) (Y : ℝ → E₄) (q : ℂ) (t : ℝ)
    (hY : HasDerivAt Y
      (circularLeadingField t (Y t)+circularBoundedField νp νm η m q (Y t)+
        (circularBoundedField νp νm η m q (circularPolynomialJet U t)-
         circularBoundedField νp νm η m (radialExteriorPolynomialFunction P t)
           (circularPolynomialJet U t))-
        circularPolynomialResidualJet νp νm η m P U t) t) :
    HasDerivAt (fun s => circularPolynomialJet U s+Y s)
      (circularLeadingField t (circularPolynomialJet U t+Y t)+
        circularBoundedField νp νm η m q (circularPolynomialJet U t+Y t)) t := by
  apply ((circularPolynomialJet_hasDerivAt νp νm η m P U t).add hY).congr_deriv
  rw [circularLeadingField_add,circularBoundedField_add]
  abel

theorem exists_circularPolynomial_solution (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (P : ℂ[X]) (U : ℂ[X] × ℂ[X]) (M κ T : ℝ) (q : ℝ → ℂ)
    (hq : Continuous q) (hqM : ∀ t, ‖q t‖ ≤ M)
    (hκ : circularFieldBound νp νm η m M < κ) (r : CircularTailSpace)
    (hr : ∀ t, T ≤ t → Real.exp (-κ*t) • circularTailEvaluation r t=
      (circularBoundedField νp νm η m (q t) (circularPolynomialJet U t)-
       circularBoundedField νp νm η m (radialExteriorPolynomialFunction P t)
         (circularPolynomialJet U t))-
        circularPolynomialResidualJet νp νm η m P U t) :
    ∃ v : CircularTailSpace,
      ‖v‖ ≤ ‖r‖/(κ-circularFieldBound νp νm η m M) ∧
      ∀ t, T ≤ t →
      HasDerivAt (fun s => circularPolynomialJet U s+circularUnweight κ v s)
        (circularLeadingField t (circularPolynomialJet U t+circularUnweight κ v t)+
          circularBoundedField νp νm η m (q t)
            (circularPolynomialJet U t+circularUnweight κ v t)) t := by
  obtain ⟨v,hv,hd⟩ := exists_circular_correction νp νm η m hm M κ q hq hqM hκ r
  refine ⟨v,hv,?_⟩
  intro t ht
  apply circularPolynomial_corrected νp νm η m P U (circularUnweight κ v) (q t) t
  simpa only [hr t ht,add_sub_assoc] using
    circularUnweight_hasDerivAt κ t νp νm η m (q t) v (circularTailEvaluation r t) (hd t)

end DefocusingNLS

end OAI
