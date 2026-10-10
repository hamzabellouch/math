import OAI.NumberTheory.CubicMoment.Angular.AngularDivisorNoncubeTotal
import OAI.NumberTheory.CubicMoment.Angular.AngularHeightDivisorBounds
import OAI.NumberTheory.CubicMoment.Angular.AngularDivisorFullModel
import OAI.NumberTheory.CubicMoment.Estimates.SieveTruncationScale

namespace OAI

/-! Sum the proved full-variance model over the actual logarithmic
square-divisor sieve. All joined divisors lie in the uniform small
range, and the finite summation costs only a fixed logarithmic power. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_sieved_full_model_asymptotic (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k U b : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (G : ℕ) (K T₀ : ℝ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (e : Eisenstein) (u : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/16) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      ‖sievedDispersionVariance (squarefreeDivisorTruncation ((1+Real.log (L r))^b))
          (fullSquarefreePrimeSupport R (W r) X e) (angularHeightPrimeCoefficient ℓ R (W r) X) u V A-
        (finiteSieveDensity (squarefreeDivisorTruncation ((1+Real.log (L r))^b)):ℂ)*
          cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
            (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη1,hσ,hgram⟩ := angular_divisor_full_model_asymptotic ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ V hV hV' (k+2*b) U
  have ha : 0 < min (η/16) c := lt_min (by positivity) hc
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp (eventually_logPower_le_rpow ha (2*b))
  refine ⟨η,σ,hη,hη1,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨G,K,T₂,hK,hgram⟩ := hgram L W hL hW hlo hhi
  refine ⟨G,324*K,max T₁ T₂,by positivity,?_⟩
  intro r X A e u hT hprod hrough hAlo hAhi he heN hu
  let z := 1+Real.log (L r)
  let D := z^b
  let S := fullSquarefreePrimeSupport R (W r) X e
  let β := angularHeightPrimeCoefficient ℓ R (W r) X
  let T := squarefreeDivisorTruncation D
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz1 : 1 ≤ z := by dsimp [z]; linarith [Real.log_nonneg (hL r)]
  have hz : 0 < z := zero_lt_one.trans_le hz1
  have hD : 0 < D := pow_pos hz b
  have hA : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hsmall : D^2 ≤ (L r)^(min (η/16) c) := by
    simpa only [D,←pow_mul,Nat.mul_comm] using hT₁ (L r) ((le_max_left _ _).trans hT)
  have hjoin (p q : Eisenstein) (hp : p ∈ T) (hq : q ∈ T) :
      norm (primarySquarefreeJoin p q) ≤ (L r)^(min (η/16) c) :=
    (squarefreeTruncation_join_norm hD.le hp hq).trans hsmall
  have herror (p : Eisenstein) (hp : p ∈ T) (q : Eisenstein) (hq : q ∈ T) :
      ‖divisorDispersionVariance (primarySquarefreeJoin p q) S β u V A-
        ((1/(norm (primarySquarefreeJoin p q))^2:ℝ):ℂ)*cubeModelTerm S β u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/z^(k+2*b) := by
    have hp' := squarefreeTruncation_spec D p hp
    have hq' := squarefreeTruncation_spec D q hq
    exact hgram r X A (primarySquarefreeJoin p q) e u ((le_max_right _ _).trans hT)
      hprod hrough (primarySquarefreeJoin_primary hp'.1 hq'.1)
      (primarySquarefreeJoin_squarefree hp'.1 hq'.1)
      ((hjoin p q hp hq).trans (Real.rpow_le_rpow_of_exponent_le (hL r) (min_le_left _ _)))
      ((hjoin p q hp hq).trans (Real.rpow_le_rpow_of_exponent_le (hL r) (min_le_right _ _)))
      hAlo hAhi he heN hu
  have hh := sieved_model_error_bound T (squarefreeTruncation_spec D) S
    (fun a ha => (fullSquarefreePrimeSupport_primary R (W r) X e ha).1)
    β u V hV hV' hA (cubeModelTerm S β u V A) herror
  have hcard : (T.card:ℝ)^2 ≤ (18*D)^2 :=
    pow_le_pow_left₀ (by positivity) (squarefreeDivisorTruncation_card_le hD.le) 2
  apply hh.trans ((mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq ?_)
  change (18*z^b)^2*(K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/z^(k+2*b)) =
    (324*K)*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/z^k
  rw [mul_pow,←pow_mul,show b*2 = 2*b by omega,pow_add]
  field_simp
  ring

end CubicFirstMoment

end

end OAI
