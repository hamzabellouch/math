import OAI.NumberTheory.CubicMoment.Estimates.FixedAngularHecke
import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorCharacter

namespace OAI

/-!
# Fixed-angular prime estimates for the literal ramified numerator

This is the nonexceptional degree-two specialization of Kaneko--Thorner,
*Highly uniform prime number theorems*, Ann. Inst. Fourier 75 (2025),
Theorem 1.2, pp.1904--1905 (Iwaniec--Kowalski, Theorem 5.13), with the
fixed-type zero-free region of Rajan (1998), Proposition 1 and Section 1.
The finite character is `cubicNumeratorChar` of modulus `9*v`; its
identification on primary elements is proved from
`CubicSupplementaryPeriodicity` in `CubicNumeratorCharacter`.

The analytic conductor majorant is
`3 * N(9*v) * (|ell|/2+3) * (|ell|/2+4)`:
`N(9*v)=81*N(v)`, so its constant is 243. The nonzero angular type
excludes a principal/exceptional-real character. The raw input below
retains the exponential conductor error and the prime-power deletion
term. Logarithmic and weighted estimates are deductions, not inputs.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def angularKummerCharacter (ℓ : ℤ) (v p : Eisenstein) : ℂ :=
  theta ℓ p*cubicSymbol p v

def angularKummerConductorFactor (ℓ : ℤ) : ℝ :=
  9*angularConductorFactor ℓ

def angularKummerAnalyticConductor (ℓ : ℤ) (v : Eisenstein) : ℝ :=
  angularKummerConductorFactor ℓ*norm v

lemma angularKummerConductorFactor_ge_one (ℓ : ℤ) :
    1 ≤ angularKummerConductorFactor ℓ := by
  have h := angularConductorFactor_ge_one ℓ
  unfold angularKummerConductorFactor
  linarith

lemma angularKummerAnalyticConductor_ge_one (ℓ : ℤ) {v : Eisenstein}
    (hv : v ≠ 0) : 1 ≤ angularKummerAnalyticConductor ℓ v := by
  have hn : (1:ℝ) ≤ norm v := by
    rw [←normNat_cast]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero hv)
  unfold angularKummerAnalyticConductor
  nlinarith [angularKummerConductorFactor_ge_one ℓ]

/-- Precisely the raw fixed-angular prime Chebyshev estimate for the
finite numerator character, including ramification and unit factors.
No stopped-sequence, smooth-weight, or dispersion conclusion is assumed. -/
def AngularKummerPrimeExplicitEstimate : Prop :=
  ∀ ℓ : ℤ, ℓ ≠ 0 → ∃ B c : ℝ, 0 < B ∧ 0 < c ∧
    ∀ v : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      ∀ x : ℝ, 3 ≤ x →
        ‖primeChebyshev (angularKummerCharacter ℓ v) x‖ ≤
          B*(heckeExponentialError c x (angularKummerAnalyticConductor ℓ v)+
            Real.sqrt x*(Real.log x)^2)

lemma angularKummerCharacter_eq_residue (hperiod : CubicSupplementaryPeriodicity)
    (ℓ : ℤ) {v p : Eisenstein} (hv : v ≠ 0) (hp : primary p) :
    angularKummerCharacter ℓ v p =
      theta ℓ p*cubicNumeratorChar hperiod v hv (Ideal.Quotient.mk (modulus (9*v)) p) := by
  rw [cubicNumeratorChar_primary hperiod v hv hp]
  rfl

theorem angular_kummer_chebyshev_logSaving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (A D : ℝ) (_hA : 0 < A) (_hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
      ∀ x : ℝ, X₀ ≤ x → ∀ v : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
        norm v ≤ (Real.log x) ^ A →
        ‖primeChebyshev (angularKummerCharacter ℓ v) x‖ ≤ C * x / (Real.log x) ^ D := by
  obtain ⟨B, c, hB, hc, hbound⟩ := hEF ℓ hℓ
  have hK : 0 < angularKummerConductorFactor ℓ := zero_lt_one.trans_le (angularKummerConductorFactor_ge_one ℓ)
  have herr := heckeExponentialError_logSaving (K := angularKummerConductorFactor ℓ)
    (A := A) (D := D) hc hK
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (herr.and (sqrt_logSq_logSaving D))
  refine ⟨17 * B, max X₁ 3, by positivity, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx v hv hnc hcon
  have hx₁ : X₁ ≤ x := (le_max_left _ _).trans hx
  have hx₃ : 3 ≤ x := (le_max_right _ _).trans hx
  have he := (hX₁ x hx₁).1 (angularKummerAnalyticConductor ℓ v)
    (angularKummerAnalyticConductor_ge_one ℓ hv)
    (mul_le_mul_of_nonneg_left hcon hK.le)
  calc
    _ ≤ B * (16 * x / (Real.log x) ^ D + x / (Real.log x) ^ D) :=
      (hbound v hv hnc x hx₃).trans
        (mul_le_mul_of_nonneg_left (add_le_add he (hX₁ x hx₁).2) hB.le)
    _ = _ := by ring

/-- Partial summation removes the logarithmic prime weight, permitting
smooth weights and norm phases. The derivative cost is retained exactly. -/
theorem weighted_angular_kummer_prime_log_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
      ∀ a b : ℝ, X₀ ≤ a → a ≤ b → ∀ v : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
        norm v ≤ (Real.log a) ^ A → ∀ f : ℝ → ℂ,
          (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun t => f t / (Real.log t : ℂ)) t) →
          IntegrableOn (deriv (fun t => f t / (Real.log t : ℂ))) (Set.Icc a b) →
          ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p),
            f (norm p) * angularKummerCharacter ℓ v p‖ ≤
          (C * b / (Real.log a) ^ D) *
            (‖f a / (Real.log a : ℂ)‖ + ‖f b / (Real.log b : ℂ)‖ +
              ∫ t in Set.Ioc a b, ‖deriv (fun t => f t / (Real.log t : ℂ)) t‖) := by
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ := angular_kummer_chebyshev_logSaving hEF ℓ hℓ A D hA hD
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro a b ha hab v hv hnc hcon f hdiff hderiv
  have ha₁ : 1 < a := hX₀.trans_le ha
  have ha₀ : 0 < a := zero_lt_one.trans ha₁
  have hprefix : ∀ t ∈ Set.Icc a b,
      ‖primeCutoffSum (fun p => angularKummerCharacter ℓ v p * (Real.log (norm p) : ℂ)) t‖ ≤
        C * b / (Real.log a) ^ D := by
    intro t ht
    have ht₀ : 0 < t := ha₀.trans_le ht.1
    have hlog : Real.log a ≤ Real.log t := Real.log_le_log ha₀ ht.1
    have hcon' : norm v ≤ (Real.log t) ^ A :=
      hcon.trans (Real.rpow_le_rpow (Real.log_pos ha₁).le hlog hA.le)
    apply (hbound t (ha.trans ht.1) v hv hnc hcon').trans
    exact div_le_div₀ (mul_nonneg hC.le (ht₀.le.trans ht.2))
      (mul_le_mul_of_nonneg_left ht.2 hC.le)
      (Real.rpow_pos_of_pos (Real.log_pos ha₁) D)
      (Real.rpow_le_rpow (Real.log_pos ha₁).le hlog hD.le)
  have h := weighted_prime_bound
    (fun p => angularKummerCharacter ℓ v p * (Real.log (norm p) : ℂ))
    (fun t => f t / (Real.log t : ℂ)) ha₀.le hab hdiff hderiv hprefix
  convert h using 2
  apply Finset.sum_congr rfl
  intro p hp
  have hp₁ : 1 < norm p := ha₁.trans (Finset.mem_filter.mp hp).2
  have hlog : (Real.log (norm p) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hp₁).ne'
  field_simp


end CubicFirstMoment

end

end OAI
