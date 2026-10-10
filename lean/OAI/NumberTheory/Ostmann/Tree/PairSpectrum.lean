import OAI.NumberTheory.Ostmann.Tree.MellinSquare
import OAI.NumberTheory.Ostmann.Tree.PairEnergy
import OAI.NumberTheory.Ostmann.Tree.ReciprocalTwist

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

def pairSpectrum (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (d : ZMod p) : ℂ :=
  ((p:ℂ)/(Fintype.card (ZMod p)ˣ:ℂ))*autocorrelation (characterTwist g χ) d

def pairWeight (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) : ℝ :=
  ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*‖fourier (characterTwist g χ) a‖^2

def pairFourthMass (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) : ℝ :=
  ∑ a : ZMod p, pairWeight g χ a ^ 2

theorem characterTwist_norm (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (hg0 : g 0=0) (x : ZMod p) : ‖characterTwist g χ x‖=‖g x‖ := by
  by_cases hx : x=0
  · simp [characterTwist,hx,hg0]
  · have hχ := mulChar_norm_unit χ (Units.mk0 x hx)
    change ‖χ x‖=1 at hχ
    simp only [characterTwist, norm_mul, Complex.norm_conj, hχ, mul_one]

theorem characterTwist_l2Sq (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (hg0 : g 0=0) : l2Sq (characterTwist g χ)=l2Sq g := by
  simp only [l2Sq, characterTwist_norm g χ hg0]

theorem pairSpectrum_unit (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (d : (ZMod p)ˣ) (hg0 : g 0=0) :
    pairSpectrum g χ d=mellin (fun t : (ZMod p)ˣ => bottomPair g d t) χ :=
  (bottomPair_mellin g χ d hg0).symm

theorem pairSpectrum_zero (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (hg0 : g 0=0) :
    pairSpectrum g χ 0 =
      ((((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*l2Sq g : ℝ):ℂ) := by
  rw [pairSpectrum, autocorrelation_zero, characterTwist_l2Sq g χ hg0]
  push_cast
  rfl

theorem fourier_pairSpectrum (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    fourier (pairSpectrum g χ) a = (pairWeight g χ a : ℂ) := by
  unfold pairSpectrum
  rw [fourier_const_mul, fourier_autocorrelation]
  simp only [pairWeight]
  push_cast
  rfl

theorem pairWeight_nonneg (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    0 ≤ pairWeight g χ a := by unfold pairWeight; positivity

theorem pairWeight_mass (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (hg0 : g 0=0) :
    ∑ a : ZMod p, pairWeight g χ a =
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*l2Sq g := by
  simp only [pairWeight, ← Finset.mul_sum, fourier_parseval, characterTwist_l2Sq g χ hg0]

theorem norm_fourier_characterTwist_le (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (a : ZMod p) : ‖fourier (characterTwist g χ) a‖ ≤ (correlationBound g:ℝ) := by
  change ‖fourier (fun x => g x*conj (χ x)) a‖ ≤ _
  have h := norm_mixedCorrelation_le g (star χ) (-a)
  rw [mixedCorrelation_eq_fourier] at h
  simpa only [neg_neg, MulChar.star_apply, RCLike.star_def] using h

theorem pairWeight_le (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    pairWeight g χ a ≤
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*(correlationBound g:ℝ)^2 := by
  apply mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_fourier_characterTwist_le g χ a) 2)
  positivity

theorem pairFourthMass_le (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (hg0 : g 0=0) :
    pairFourthMass g χ ≤
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2 * (correlationBound g:ℝ)^2 * l2Sq g := by
  have hpoint (a : ZMod p) : pairWeight g χ a ^2 ≤
      (((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*(correlationBound g:ℝ)^2)*pairWeight g χ a := by
    have h := mul_le_mul_of_nonneg_right (pairWeight_le g χ a) (pairWeight_nonneg g χ a)
    simpa only [pow_two] using h
  apply (Finset.sum_le_sum (fun a _ => hpoint a)).trans
  rw [← Finset.mul_sum, pairWeight_mass g χ hg0]
  exact le_of_eq (by ring)

theorem pairFourthMass_eq_l2Sq (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) :
    pairFourthMass g χ = l2Sq (pairSpectrum g χ) := by
  rw [← fourier_parseval]
  simp only [pairFourthMass, fourier_pairSpectrum, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end
end Ostmann.FiniteField

end OAI
