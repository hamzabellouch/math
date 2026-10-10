import OAI.Analysis.KadisonKastler.DoubleGaussianFixed
import OAI.Analysis.KadisonKastler.DoubleGaussianCovariance
import OAI.Analysis.KadisonKastler.GaussianInjective

namespace OAI

/-! # Uniqueness of commuting KMS actions for a faithful vector state -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (Ω : H)
  (U V : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

include hU hV in
theorem commuting_kms_actions_eq
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hnU : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hnV : ∀ t a, a ∈ M → unitaryConj (V t) a ∈ M)
    (hcomm : ∀ s t, Commute (U s : H →L[ℂ] H) (V t : H →L[ℂ] H))
    (hKU : VectorStateKMS M Ω U) (hKV : VectorStateKMS M Ω V)
    (a : H →L[ℂ] H) (ha : a ∈ M) (t : ℝ) :
    unitaryConj (U (Multiplicative.ofAdd t)) a = unitaryConj (V (Multiplicative.ofAdd t)) a := by
  let D := doubleGaussianStateAverage U V hU hV a 1 zero_lt_one 0 0
  have hfix : unitaryConj (U (Multiplicative.ofAdd t))
      (unitaryConj (V (Multiplicative.ofAdd (-t))) D) = D := by
    rw [doubleGaussian_second_covariance U V hU hV hcomm,
      doubleGaussian_first_covariance]
    simpa only [zero_add, Complex.ofReal_neg] using
      doubleGaussian_diagonal_fixed Ω U V hU hV hsep hnU hnV hcomm hKU hKV a ha 1 zero_lt_one t
  have he := congrArg (unitaryConj (V (Multiplicative.ofAdd t))) hfix
  rw [unitaryConj_commute _ _ (hcomm _ _).symm] at he
  have hc : unitaryConj (V (Multiplicative.ofAdd t))
      (unitaryConj (V (Multiplicative.ofAdd (-t))) D) = D := by
    rw [← regularGroup_star_eq V t]
    simpa only [star_star] using unitaryConj_star_unitaryConj (star (V (Multiplicative.ofAdd t))) D
  rw [hc] at he
  apply gaussianStateAverage_injective V hV 1 zero_lt_one
  apply gaussianStateAverage_injective U hU 1 zero_lt_one
  change doubleGaussianStateAverage U V hU hV _ 1 zero_lt_one 0 0 =
    doubleGaussianStateAverage U V hU hV _ 1 zero_lt_one 0 0
  rw [← doubleGaussian_conjugate U V hU hV _ (unitaryRealGroup_commute U _) (hcomm _),
    ← doubleGaussian_conjugate U V hU hV _ (fun s => (hcomm s _).symm) (unitaryRealGroup_commute V _)]
  exact he

end

end KadisonKastler

end OAI
