import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeFromPrimitive
import OAI.NumberTheory.CubicMoment.Estimates.PrimeChebyshevTrivial

namespace OAI

/-! The explicit angular prime estimate, including the bounded initial
range, derived from primitive Hecke completion. -/
noncomputable section
namespace CubicFirstMoment

theorem angular_prime_explicit_of_primitive (hpub : PrimitiveAngularHeckeInput) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧
    ∀ (q : Eisenstein), q ≠ 0 → (3:Eisenstein) ∣ q →
    ∀ (χ : MulChar (Residues q) ℂ) (ℓ : ℤ), ℓ ≠ 0 → AngularUnitCompatible q χ ℓ →
    ∀ Q : ℝ, 1 ≤ Q → norm q ≤ Q → |(ℓ:ℝ)|+7 ≤ Q →
    ∀ X : ℝ, 3 ≤ X →
      ‖primeChebyshev (fun p => χ (Ideal.Quotient.mk (modulus q) p)*theta ℓ p) X‖ ≤
        B*(heckeExponentialError c X Q+Real.sqrt X*(Real.log X)^2) := by
  obtain ⟨B,c,X0,hB,hc,hX0,hbound⟩ := angular_prime_from_primitive hpub
  refine ⟨B+18*X0,c,by positivity,hc,?_⟩
  intro q hq h3 χ ℓ hℓ hu Q hQ hqQ hkQ X hX
  have hE : 0 ≤ heckeExponentialError c X Q := by unfold heckeExponentialError; positivity
  have hS : 0 ≤ Real.sqrt X*(Real.log X)^2 := by positivity
  by_cases hlarge : X0 ≤ X
  · have hh := hbound q hq h3 χ ℓ hℓ hu Q hQ hqQ hkQ X hlarge
    nlinarith [mul_nonneg (by positivity : 0 ≤ 18*X0) hE,
      mul_nonneg (by positivity : 0 ≤ B+18*X0) hS]
  · have hh := primeChebyshev_bounded_range (fun p => χ (Ideal.Quotient.mk (modulus q) p)*theta ℓ p)
      (fun p hp => by
        rw [norm_mul,norm_theta hp.2.ne_zero ℓ,mul_one]
        exact residueChar_norm_le_one hq χ _) hX (le_of_not_ge hlarge)
    nlinarith [mul_nonneg hB.le hS,mul_nonneg (by positivity : 0 ≤ B+18*X0) hE]

lemma angularConductor_controls (ℓ : ℤ) {v : Eisenstein} (hv : v ≠ 0) :
    norm (3*v) ≤ angularConductorFactor ℓ*norm v ∧
      |(ℓ:ℝ)|+7 ≤ angularConductorFactor ℓ*norm v := by
  have hn := one_le_norm hv
  have hk := abs_nonneg (ℓ:ℝ)
  have hP : 12 ≤ (|(ℓ:ℝ)|/2+3)*(|(ℓ:ℝ)|/2+4) := by nlinarith
  have hheight : |(ℓ:ℝ)|+7 ≤ angularConductorFactor ℓ := by
    unfold angularConductorFactor
    nlinarith
  have hF : 9 ≤ angularConductorFactor ℓ := by unfold angularConductorFactor; nlinarith
  have h3 : norm (3:Eisenstein)=9 := by change Complex.normSq (3:ℂ)=9; norm_num
  constructor
  · rw [norm_mul_eq,h3]
    exact mul_le_mul_of_nonneg_right hF (by linarith)
  · exact hheight.trans (le_mul_of_one_le_right (by linarith) hn)

end CubicFirstMoment

end

end OAI
