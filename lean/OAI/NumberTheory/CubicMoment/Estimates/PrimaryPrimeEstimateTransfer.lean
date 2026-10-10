import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeEulerExclusion
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerAbsorption

namespace OAI

/-! The finite loss in restoring the original modulus is absorbed in
the same explicit prime majorant. No new analytic estimate is needed. -/
noncomputable section
namespace CubicFirstMoment

lemma angularResidueIdealChar_zero (q : Eisenstein) (χ : MulChar (Residues q) ℂ) :
    angularResidueIdealChar q χ 0=residueIdealChar q χ := by
  funext ν
  simp only [angularResidueIdealChar,theta_zero,mul_one]

lemma primeCancellation_log_cost {c Q X : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1/4)
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X) :
    Real.log Q ≤ primeCancellationWeight c Q X := by
  have hX1 : 1 ≤ X := by
    have hh := Real.exp_le_exp.mpr (show (0:ℝ) ≤ Real.log X by linarith)
    simpa [Real.exp_log hXp] using hh
  have hroot : Real.sqrt X ≤ X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hXp.le,by nlinarith⟩
  have hs := primeDyadic_sqrt_absorption (c := 2*c) (by linarith : 0 ≤ 2*c)
    (by linarith : 2*c ≤ 1/2) hQ hXp hX hroot le_rfl
  rw [show 2*c/2=c by ring] at hs
  have hroot1 : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hXp.le).mpr (by simpa using hX1)
  have hv : 1 ≤ X*Real.exp (-c*Real.log X/primeContourDenominator Q X) := hroot1.trans hs
  have hP := (primeLogSize_bounds hQ hXp (by linarith)).1
  have hq : Real.log Q ≤ Real.log (X*Q) := by
    rw [Real.log_mul hXp.ne' (show Q ≠ 0 by linarith)]
    linarith
  calc
    _ ≤ (Real.log (X*Q))^2 := by nlinarith
    _ ≤ (X*Real.exp (-c*Real.log X/primeContourDenominator Q X))*(Real.log (X*Q))^2 :=
      le_mul_of_one_le_left (sq_nonneg _) hv
    _ = _ := by unfold primeCancellationWeight; ring

theorem primary_angular_prime_bound_of_primitive {q d : Eisenstein}
    (hq : q ≠ 0) (hd : d ≠ 0) (h3 : (3:Eisenstein) ∣ q)
    (χ : MulChar (Residues q) ℂ) (ψ : MulChar (Residues d) ℂ)
    (hi : ResidueCharacterInduces q d χ ψ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    {B c Q X : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1/4) (hQ : 1 ≤ Q)
    (hqQ : norm q ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (hmain : ‖idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X‖ ≤ B*primeCancellationWeight c Q X) :
    ‖primeChebyshev (fun p => χ (Ideal.Quotient.mk (modulus q) p)*theta ℓ p) X‖ ≤
      (B+1)*primeCancellationWeight c Q X := by
  have herr := (induced_angular_prime_error hq hd hi ℓ X).trans
    ((Real.log_le_log (norm_pos_of_ne_zero hq) hqQ).trans (primeCancellation_log_cost hc hc1 hQ hXp hX))
  rw [angular_primeChebyshev_eq_ideal h3 χ ℓ hu]
  calc
    _ = ‖idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X+
        (idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X-
          idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X)‖ := by
      congr 1
      abel
    _ ≤ ‖idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X‖+
        ‖idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X-
          idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X‖ := norm_add_le _ _
    _ ≤ B*primeCancellationWeight c Q X+primeCancellationWeight c Q X := add_le_add hmain herr
    _ = _ := by ring

lemma residue_primeChebyshev_eq_ideal {q : Eisenstein} (h3 : (3:Eisenstein) ∣ q)
    (χ : MulChar (Residues q) ℂ)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u)=1) (X : ℝ) :
    primeChebyshev (fun p => χ (Ideal.Quotient.mk (modulus q) p)) X =
      idealPrimeChebyshev (residueIdealChar q χ) X := by
  have hu0 : AngularUnitCompatible q χ 0 := by
    intro u
    rw [theta_zero,mul_one,hu u]
  have hh := angular_primeChebyshev_eq_ideal h3 χ 0 hu0 X
  simpa only [theta_zero,mul_one,angularResidueIdealChar_zero] using hh

end CubicFirstMoment

end

end OAI
