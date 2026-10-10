import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveAngularPrimeEstimate
import OAI.NumberTheory.CubicMoment.Estimates.PrimeConductorComparison

namespace OAI

/-! Primitive reduction, finite Euler restoration, and the literal
primary-prime sum with a fixed nonzero angular frequency. -/
noncomputable section
namespace CubicFirstMoment

theorem angular_prime_from_primitive (hpub : PrimitiveAngularHeckeInput) :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ 1 < X0 ∧
    ∀ (q : Eisenstein), q ≠ 0 → (3:Eisenstein) ∣ q →
    ∀ (χ : MulChar (Residues q) ℂ) (ℓ : ℤ), ℓ ≠ 0 → AngularUnitCompatible q χ ℓ →
    ∀ Q : ℝ, 1 ≤ Q → norm q ≤ Q → |(ℓ:ℝ)|+7 ≤ Q →
    ∀ X : ℝ, X0 ≤ X →
      ‖primeChebyshev (fun p => χ (Ideal.Quotient.mk (modulus q) p)*theta ℓ p) X‖ ≤
        B*heckeExponentialError c X Q := by
  obtain ⟨B,c,Y0,hB,hc,hc1,hY0,hbound⟩ := primitive_angular_prime_ideal_estimate hpub
  let X0 := max Y0 (Real.exp 2)
  refine ⟨25*(B+1),c/5,X0,by positivity,by positivity,hY0.trans_le (le_max_left _ _),?_⟩
  intro q hq h3 χ ℓ hℓ hu Q hQ hqQ hkQ X hX
  obtain ⟨d,ψ,hd,hi,hN,hp⟩ := primitive_residue_conductor_exists hq χ
  have hnd : norm d ≤ norm q := by
    simpa only [normNat_cast] using (Nat.cast_le.mpr hN : (normNat d:ℝ) ≤ (normNat q:ℝ))
  have hdQ : norm d ≤ Q := hnd.trans hqQ
  have hR : 1 ≤ 4*Q^2 := by nlinarith
  have hQR : Q ≤ 4*Q^2 := by nlinarith
  have hNR : 2*norm d*(1+norm d) ≤ 4*Q^2 := by
    calc
      _ ≤ 2*Q*(1+Q) := by gcongr; linarith [norm_nonneg d]
      _ ≤ _ := by nlinarith
  have hm := hbound d hd ψ hp ℓ hℓ (hi.angular_units hu) (4*Q^2) hR hNR
    (hkQ.trans hQR) X ((le_max_left _ _).trans hX)
  have hXe : Real.exp 2 ≤ X := (le_max_right _ _).trans hX
  have hXp : 0 < X := (Real.exp_pos 2).trans_le hXe
  have hL : 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) hXe
    rwa [Real.log_exp] at hh
  have hh := primary_angular_prime_bound_of_primitive hq hd h3 χ ψ hi ℓ hu
    hc.le hc1 hR (hqQ.trans hQR) hXp hL hm
  calc
    _ ≤ (B+1)*primeCancellationWeight c (4*Q^2) X := hh
    _ ≤ (B+1)*(25*heckeExponentialError (c/5) X Q) := mul_le_mul_of_nonneg_left
      (primeCancellation_polynomial_conductor hc.le hQ hXp (by linarith)) (by linarith)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
